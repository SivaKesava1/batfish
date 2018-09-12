package org.batfish.question;

import static com.google.common.base.MoreObjects.firstNonNull;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.auto.service.AutoService;
import com.google.common.base.Strings;
import com.google.common.collect.Sets;
import com.google.common.collect.SortedSetMultimap;
import com.google.common.collect.TreeMultimap;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.lang.Math;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Map.Entry;
import java.util.NavigableMap;
import java.util.Random;
import java.util.regex.Pattern;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.common.util.CommonUtil;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.BgpPeerConfig;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Interface;
import org.batfish.datamodel.InterfaceAddress;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.questions.INodeRegexQuestion;
import org.batfish.datamodel.questions.NodesSpecifier;
import org.batfish.datamodel.questions.Question;
import org.batfish.datamodel.questions.smt.HeaderQuestion;
import org.batfish.question.SmtBlackholeQuestionPlugin.BlackholeQuestion;

@AutoService(Plugin.class)
public class InterfaceMatchingQuestionPlugin extends QuestionPlugin {

  public static class InterfaceMatchingAnswerElement extends AnswerElement{
    
    public static final String PROP_ASNS = "asns";

    private String _asns;
    
    public InterfaceMatchingAnswerElement(@JsonProperty(PROP_ASNS) String asns) {
      _asns = new String(asns);
    }
    
    @JsonProperty(PROP_ASNS)
    public String getAsns() {
      return _asns;
    }
    
    @Override
    public String prettyPrint() {
      StringBuilder sb = new StringBuilder("Results for IP Based Matching\n");
      if (_asns != null) {
        sb.append(_asns);
      }
      return sb.toString();
    }
    
  }
  
  public static class InterfaceMatchingAnswerer extends Answerer {

    public InterfaceMatchingAnswerer(Question question, IBatfish batfish) {
      super(question, batfish);
    }
    
    public class HungarianAlgorithm {
      private final double[][] costMatrix;
      private final int rows, cols, dim;
      private final double[] labelByWorker, labelByJob;
      private final int[] minSlackWorkerByJob;
      private final double[] minSlackValueByJob;
      private final int[] matchJobByWorker, matchWorkerByJob;
      private final int[] parentWorkerByCommittedJob;
      private final boolean[] committedWorkers;

      /**
       * Construct an instance of the algorithm.
       * 
       * @param costMatrix
       *          the cost matrix, where matrix[i][j] holds the cost of assigning
       *          worker i to job j, for all i, j. The cost matrix must not be
       *          irregular in the sense that all rows must be the same length; in
       *          addition, all entries must be non-infinite numbers.
       */
      public HungarianAlgorithm(double[][] costMatrix) {
        this.dim = Math.max(costMatrix.length, costMatrix[0].length);
        this.rows = costMatrix.length;
        this.cols = costMatrix[0].length;
        this.costMatrix = new double[this.dim][this.dim];
        for (int w = 0; w < this.dim; w++) {
          if (w < costMatrix.length) {
            if (costMatrix[w].length != this.cols) {
              throw new IllegalArgumentException("Irregular cost matrix");
            }
            for (int j = 0; j < this.cols; j++) {
              if (Double.isInfinite(costMatrix[w][j])) {
                throw new IllegalArgumentException("Infinite cost");
              }
              if (Double.isNaN(costMatrix[w][j])) {
                throw new IllegalArgumentException("NaN cost");
              }
            }
            this.costMatrix[w] = Arrays.copyOf(costMatrix[w], this.dim);
          } else {
            this.costMatrix[w] = new double[this.dim];
          }
        }
        labelByWorker = new double[this.dim];
        labelByJob = new double[this.dim];
        minSlackWorkerByJob = new int[this.dim];
        minSlackValueByJob = new double[this.dim];
        committedWorkers = new boolean[this.dim];
        parentWorkerByCommittedJob = new int[this.dim];
        matchJobByWorker = new int[this.dim];
        Arrays.fill(matchJobByWorker, -1);
        matchWorkerByJob = new int[this.dim];
        Arrays.fill(matchWorkerByJob, -1);
      }

      /**
       * Compute an initial feasible solution by assigning zero labels to the
       * workers and by assigning to each job a label equal to the minimum cost
       * among its incident edges.
       */
      protected void computeInitialFeasibleSolution() {
        for (int j = 0; j < dim; j++) {
          labelByJob[j] = Double.POSITIVE_INFINITY;
        }
        for (int w = 0; w < dim; w++) {
          for (int j = 0; j < dim; j++) {
            if (costMatrix[w][j] < labelByJob[j]) {
              labelByJob[j] = costMatrix[w][j];
            }
          }
        }
      }

      /**
       * Execute the algorithm.
       * 
       * @return the minimum cost matching of workers to jobs based upon the
       *         provided cost matrix. A matching value of -1 indicates that the
       *         corresponding worker is unassigned.
       */
      public int[] execute() {
        /*
         * Heuristics to improve performance: Reduce rows and columns by their
         * smallest element, compute an initial non-zero dual feasible solution and
         * create a greedy matching from workers to jobs of the cost matrix.
         */
        reduce();
        computeInitialFeasibleSolution();
        greedyMatch();

        int w = fetchUnmatchedWorker();
        while (w < dim) {
          initializePhase(w);
          executePhase();
          w = fetchUnmatchedWorker();
        }
        int[] result = Arrays.copyOf(matchJobByWorker, rows);
        for (w = 0; w < result.length; w++) {
          if (result[w] >= cols) {
            result[w] = -1;
          }
        }
        return result;
      }

      /**
       * Execute a single phase of the algorithm. A phase of the Hungarian algorithm
       * consists of building a set of committed workers and a set of committed jobs
       * from a root unmatched worker by following alternating unmatched/matched
       * zero-slack edges. If an unmatched job is encountered, then an augmenting
       * path has been found and the matching is grown. If the connected zero-slack
       * edges have been exhausted, the labels of committed workers are increased by
       * the minimum slack among committed workers and non-committed jobs to create
       * more zero-slack edges (the labels of committed jobs are simultaneously
       * decreased by the same amount in order to maintain a feasible labeling).
       * <p>
       * 
       * The runtime of a single phase of the algorithm is O(n^2), where n is the
       * dimension of the internal square cost matrix, since each edge is visited at
       * most once and since increasing the labeling is accomplished in time O(n) by
       * maintaining the minimum slack values among non-committed jobs. When a phase
       * completes, the matching will have increased in size.
       */
      protected void executePhase() {
        while (true) {
          int minSlackWorker = -1, minSlackJob = -1;
          double minSlackValue = Double.POSITIVE_INFINITY;
          for (int j = 0; j < dim; j++) {
            if (parentWorkerByCommittedJob[j] == -1) {
              if (minSlackValueByJob[j] < minSlackValue) {
                minSlackValue = minSlackValueByJob[j];
                minSlackWorker = minSlackWorkerByJob[j];
                minSlackJob = j;
              }
            }
          }
          if (minSlackValue > 0) {
            updateLabeling(minSlackValue);
          }
          parentWorkerByCommittedJob[minSlackJob] = minSlackWorker;
          if (matchWorkerByJob[minSlackJob] == -1) {
            /*
             * An augmenting path has been found.
             */
            int committedJob = minSlackJob;
            int parentWorker = parentWorkerByCommittedJob[committedJob];
            while (true) {
              int temp = matchJobByWorker[parentWorker];
              match(parentWorker, committedJob);
              committedJob = temp;
              if (committedJob == -1) {
                break;
              }
              parentWorker = parentWorkerByCommittedJob[committedJob];
            }
            return;
          } else {
            /*
             * Update slack values since we increased the size of the committed
             * workers set.
             */
            int worker = matchWorkerByJob[minSlackJob];
            committedWorkers[worker] = true;
            for (int j = 0; j < dim; j++) {
              if (parentWorkerByCommittedJob[j] == -1) {
                double slack = costMatrix[worker][j] - labelByWorker[worker]
                    - labelByJob[j];
                if (minSlackValueByJob[j] > slack) {
                  minSlackValueByJob[j] = slack;
                  minSlackWorkerByJob[j] = worker;
                }
              }
            }
          }
        }
      }

      /**
       * 
       * @return the first unmatched worker or {@link #dim} if none.
       */
      protected int fetchUnmatchedWorker() {
        int w;
        for (w = 0; w < dim; w++) {
          if (matchJobByWorker[w] == -1) {
            break;
          }
        }
        return w;
      }

      /**
       * Find a valid matching by greedily selecting among zero-cost matchings. This
       * is a heuristic to jump-start the augmentation algorithm.
       */
      protected void greedyMatch() {
        for (int w = 0; w < dim; w++) {
          for (int j = 0; j < dim; j++) {
            if (matchJobByWorker[w] == -1 && matchWorkerByJob[j] == -1
                && costMatrix[w][j] - labelByWorker[w] - labelByJob[j] == 0) {
              match(w, j);
            }
          }
        }
      }

      /**
       * Initialize the next phase of the algorithm by clearing the committed
       * workers and jobs sets and by initializing the slack arrays to the values
       * corresponding to the specified root worker.
       * 
       * @param w
       *          the worker at which to root the next phase.
       */
      protected void initializePhase(int w) {
        Arrays.fill(committedWorkers, false);
        Arrays.fill(parentWorkerByCommittedJob, -1);
        committedWorkers[w] = true;
        for (int j = 0; j < dim; j++) {
          minSlackValueByJob[j] = costMatrix[w][j] - labelByWorker[w]
              - labelByJob[j];
          minSlackWorkerByJob[j] = w;
        }
      }

      /**
       * Helper method to record a matching between worker w and job j.
       */
      protected void match(int w, int j) {
        matchJobByWorker[w] = j;
        matchWorkerByJob[j] = w;
      }

      /**
       * Reduce the cost matrix by subtracting the smallest element of each row from
       * all elements of the row as well as the smallest element of each column from
       * all elements of the column. Note that an optimal assignment for a reduced
       * cost matrix is optimal for the original cost matrix.
       */
      protected void reduce() {
        for (int w = 0; w < dim; w++) {
          double min = Double.POSITIVE_INFINITY;
          for (int j = 0; j < dim; j++) {
            if (costMatrix[w][j] < min) {
              min = costMatrix[w][j];
            }
          }
          for (int j = 0; j < dim; j++) {
            costMatrix[w][j] -= min;
          }
        }
        double[] min = new double[dim];
        for (int j = 0; j < dim; j++) {
          min[j] = Double.POSITIVE_INFINITY;
        }
        for (int w = 0; w < dim; w++) {
          for (int j = 0; j < dim; j++) {
            if (costMatrix[w][j] < min[j]) {
              min[j] = costMatrix[w][j];
            }
          }
        }
        for (int w = 0; w < dim; w++) {
          for (int j = 0; j < dim; j++) {
            costMatrix[w][j] -= min[j];
          }
        }
      }

      /**
       * Update labels with the specified slack by adding the slack value for
       * committed workers and by subtracting the slack value for committed jobs. In
       * addition, update the minimum slack values appropriately.
       */
      protected void updateLabeling(double slack) {
        for (int w = 0; w < dim; w++) {
          if (committedWorkers[w]) {
            labelByWorker[w] += slack;
          }
        }
        for (int j = 0; j < dim; j++) {
          if (parentWorkerByCommittedJob[j] != -1) {
            labelByJob[j] -= slack;
          } else {
            minSlackValueByJob[j] -= slack;
          }
        }
      }
    }
    
    private class NodeData{
      Map<Ip, Entry<String, String>> _nodeintf;
      Map<Ip,String> _nodebgp;
      
      NodeData(Map<Ip, Entry<String, String>> nodeintf,  Map<Ip,String> nodebgp ){
        _nodeintf = new HashMap<Ip, Entry<String, String>>(nodeintf);
         _nodebgp = new HashMap<Ip,String>(nodebgp);
      }
      
    }
    
    private class Pair{
      String _node1;
      String _node2;
      int _editDistance;
      int[] _intfMap;
      int _intfScore;
      int[] _bgpMap;
      int _bgpScore;
      
      Pair(String node1, String node2, int editDistance, int[] intfMap, int intfScore,
          int[] bgpMap, int bgpScore){
        _node1 = node1;
        _node2 = node2;
        _editDistance = editDistance;
        _intfMap = intfMap;
        _intfScore = intfScore;
        _bgpMap = bgpMap;
        _bgpScore = bgpScore;
      }
      
    }
   
    
    public static int distance(String s1, String s2){
      int edits[][]=new int[s1.length()+1][s2.length()+1];
      for(int i=0;i<=s1.length();i++)
          edits[i][0]=i;
      for(int j=1;j<=s2.length();j++)
          edits[0][j]=j;
      for(int i=1;i<=s1.length();i++){
          for(int j=1;j<=s2.length();j++){
              int u=(s1.charAt(i-1)==s2.charAt(j-1)?0:1);
              edits[i][j]=Math.min(
                              edits[i-1][j]+1,
                              Math.min(
                                 edits[i][j-1]+1,
                                 edits[i-1][j-1]+u
                              )
                          );
          }
      }
      return edits[s1.length()][s2.length()];
    }
    
    
    private Map<Ip, Entry<String, String>> interface_name_mapping(NavigableMap<String, Interface> _interfaces) {  
      Map<Ip, Entry<String, String>> actionMap = new HashMap<Ip, Entry<String, String>>();
      for(Entry<String, Interface> e : _interfaces.entrySet()) {
         if (e.getValue().getAllAddresses().size() != 0){
           String name;
           if(!e.getValue().getDeclaredNames().isEmpty()) {
             name = e.getValue().getDeclaredNames().first();
           }else {
             name =e.getValue().getName();
           }         
        
          actionMap.put(e.getValue().getAllAddresses().iterator().next().getIp(), 
              new AbstractMap.SimpleEntry<String, String>(name,e.getValue().getDescription()));
        }           
      }
      return actionMap;
    }
    
    
    private Map<Ip,String> get_bgp_neighbors(Configuration c){
      Map<Ip,String> bgp_ngh = new HashMap<Ip,String>();
      for (Vrf vrf : c.getVrfs().values()) {
        if(vrf.getBgpProcess() == null) {
          continue;
        }
        BgpProcess proc = vrf.getBgpProcess();
        for (BgpActivePeerConfig neighbor : proc.getActiveNeighbors().values()) {
          if(neighbor.getPeerAddress() != null) {
          bgp_ngh.put(neighbor.getPeerAddress(), neighbor.getDescription());    
          }
      }
      }
      return bgp_ngh;
    }
      
    private Pair mapping_from_JSON(NodeData node1, NodeData node2, String node1_name, String node2_name) {

      int editDistance = distance(node1_name,node2_name);          
      
      int[] intfMap = null;
      int intfScore = 0;
      int i = 0;
      
      if(node1._nodeintf.size() == 0 ||  node2._nodeintf.size() ==0) {
        intfScore = (int) Math.pow(2, 24);
        intfMap = new int[0];
      }
      else
      {
        double[][] weight = new double[node1._nodeintf.size()][node2._nodeintf.size()];
        
        for(Ip ip1:node1._nodeintf.keySet()) {
          int j =0;
          for(Ip ip2:node2._nodeintf.keySet()) {
            weight[i][j] = Math.abs(ip1.asLong()-ip2.asLong());
            j++;
          }
          i++;
        } 
        
        HungarianAlgorithm intf_matching = new  HungarianAlgorithm(weight);
        intfMap = intf_matching.execute();
        intfScore = 0;
        for(int k =0; k < intfMap.length; k++) {
          if(intfMap[k] != -1) {
            intfScore = (int) (intfScore + weight[k][intfMap[k]]);
          }
        }
      }
      
      int bgpScore = 0;
      int[] bgpMap = null;
      
      if(node1._nodebgp.size() == 0 ||  node2._nodebgp.size() ==0) {
        bgpScore = (int) Math.pow(2, 24);
        bgpMap = new int[0];
      }
      else
      {
        double[][] weight_bgp = new double[node1._nodebgp.size()][node2._nodebgp.size()];
        i = 0;
        for(Ip ip1:node1._nodebgp.keySet()) {
          int j =0;
          for(Ip ip2:node2._nodebgp.keySet()) {
            weight_bgp[i][j] = Math.abs(ip1.asLong()-ip2.asLong());
            j++;
          }
          i++;
        } 

        HungarianAlgorithm bgp_matching = new  HungarianAlgorithm(weight_bgp);
        bgpMap = bgp_matching.execute();
       
        for(int k =0; k < bgpMap.length; k++) {
          if(bgpMap[k] != -1) {
            bgpScore = (int) (bgpScore + weight_bgp[k][bgpMap[k]]);
          }
        }
      }
 
      return new Pair(node1_name, node2_name, editDistance, intfMap, intfScore, bgpMap, bgpScore);
    }
    
    @Override
    public AnswerElement answer() {
      InterfaceMatchingQuestion question = (InterfaceMatchingQuestion) _question;
      Set<String> _nodes = question.getNodeRegex().getMatchingNodes(_batfish);
      String [] nodes = _nodes.toArray(new String[_nodes.size()]);
      System.out.println(nodes);
      Map<String, Configuration> configurations = _batfish.loadConfigurations();
      int list_size = nodes.length;
      Map<String, NodeData> requireddata = new HashMap<String,NodeData>();     
      for(String hostname: nodes) {
        Configuration node = configurations.get(hostname);
        NodeData nodedata = new NodeData(interface_name_mapping(node.getAllInterfaces()), get_bgp_neighbors(node));
        requireddata.put(hostname, nodedata);
        
      }

      List<Pair> pair_score = new ArrayList<Pair>();
      for(int i =0; i<list_size;i++) {
        for(int j =i+1; j<list_size;j++) {
          pair_score.add(mapping_from_JSON(requireddata.get(nodes[i]),requireddata.get(nodes[j]),
                        nodes[i], nodes[j]));
         
        }
      }

      pair_score.sort((p1,p2) ->  ((p1._bgpScore + p1._editDistance) - (p2._bgpScore + p2._editDistance) ));      
      StringBuilder sb = new StringBuilder("Results for BGP Neighbor Matching\n"); 
      Set<String> s = new HashSet<String>();
      for(Pair p: pair_score) {
        if(!s.contains(p._node1) ) {
          s.add(p._node1);
          sb.append("\nRouter1: " + p._node1 + "\nRouter2: "+ p._node2 + "\nBGPNghIPScore: " + p._bgpScore + "\nNameEditDistance: " +p._editDistance + "\n");
          Map<Ip,String> node1 = requireddata.get(p._node1)._nodebgp;
          Map<Ip,String> node2 = requireddata.get(p._node2)._nodebgp;
          List<Ip> keysN2 = new ArrayList<Ip>(node2.keySet());
          List<Ip> keysN1 = new ArrayList<Ip>(node1.keySet());         
          for(int i=0;i<p._bgpMap.length;i++)
          {
            if(p._bgpMap[i] != -1) {
              sb.append("R1:  (" + keysN1.get(i)+ " , "+ node1.get(keysN1.get(i)) + ")\nR2:  ("+
                  keysN2.get(p._bgpMap[i]) + " , "+ node2.get(keysN2.get(p._bgpMap[i])) + ")\n");
            }
          }
        }
        if(!s.contains(p._node2) ) {
          s.add(p._node2);
          sb.append("\nRouter1: " + p._node2 + "\nRouter2: "+ p._node1 + "\nBGPNghIPScore: " + p._bgpScore + "\nNameEditDistance: " +p._editDistance + "\n");
          Map<Ip,String> node1 = requireddata.get(p._node1)._nodebgp;
          Map<Ip,String> node2 = requireddata.get(p._node2)._nodebgp;
          List<Ip> keysN2 = new ArrayList<Ip>(node2.keySet());
          List<Ip> keysN1 = new ArrayList<Ip>(node1.keySet());    
          for(int i=0;i<p._bgpMap.length;i++)
          {
            if(p._bgpMap[i] != -1) {
              sb.append("R1:  (" + keysN2.get(p._bgpMap[i])+ " , "+ node2.get(keysN2.get(p._bgpMap[i])) + ")\nR2:  ("+
                  keysN1.get(i) + " , "+ node1.get(keysN1.get(i)) + ")\n");
            }
          }
       
        }        
      }
      pair_score.sort((p1,p2) ->  ((p1._intfScore + p1._editDistance) - (p2._intfScore + p2._editDistance) ));
      sb.append("Results for Interface Matching\n");
      s = new HashSet<String>();
      for(Pair p: pair_score) {
        if(!s.contains(p._node1) ) {
          s.add(p._node1);
          sb.append("\nRouter1: " + p._node1 + "\nRouter2: "+ p._node2 + "\nInterfaceIPScore: " + p._intfScore + "\nNameEditDistance: " +p._editDistance + "\n");
          Map<Ip, Entry<String, String>> node1 = requireddata.get(p._node1)._nodeintf;
          Map<Ip, Entry<String, String>> node2 = requireddata.get(p._node2)._nodeintf;
          List<Ip> keysN2 = new ArrayList<Ip>(node2.keySet());
          List<Ip> keysN1 = new ArrayList<Ip>(node1.keySet());         
          for(int i=0;i<p._intfMap.length;i++)
          {
            if(p._intfMap[i] != -1) {
              sb.append("R1:  (" + keysN1.get(i)+ " , "+ node1.get(keysN1.get(i)) + ")\nR2:  ("+
                  keysN2.get(p._intfMap[i]) + " , "+ node2.get(keysN2.get(p._intfMap[i])) + ")\n");
            }
          }
        }
        if(!s.contains(p._node2) ) {
          s.add(p._node2);
          sb.append("\nRouter1: " + p._node2 + "\nRouter2: "+ p._node1 + "\nInterfaceIPScore: " + p._intfScore + "\nNameEditDistance: " +p._editDistance + "\n");
          Map<Ip, Entry<String, String>> node1 = requireddata.get(p._node1)._nodeintf;
          Map<Ip, Entry<String, String>> node2 = requireddata.get(p._node2)._nodeintf;
          List<Ip> keysN2 = new ArrayList<Ip>(node2.keySet());
          List<Ip> keysN1 = new ArrayList<Ip>(node1.keySet());    
          for(int i=0;i<p._intfMap.length;i++)
          {
            if(p._intfMap[i] != -1) {
              sb.append("R1:  (" + keysN2.get(p._intfMap[i])+ " , "+ node2.get(keysN2.get(p._intfMap[i])) + ")\nR2:  ("+
                  keysN1.get(i) + " , "+ node1.get(keysN1.get(i)) + ")\n");
            }
          }
       
        }        
      }

      InterfaceMatchingAnswerElement answerElement  = new InterfaceMatchingAnswerElement(sb.toString());
      return answerElement;
    }
  }
  

  public static class InterfaceMatchingQuestion extends Question implements INodeRegexQuestion{

    private static final String PROP_NODE_REGEX = "nodeRegex";
    private NodesSpecifier _nodeRegex;
    public InterfaceMatchingQuestion( @JsonProperty(PROP_NODE_REGEX) NodesSpecifier nodeRegex) {
       _nodeRegex = firstNonNull(nodeRegex, NodesSpecifier.ALL);
    }
    
    @Override
    public boolean getDataPlane() {
      return false;
    }
    
    @Override
    public String getName() {
      return "interfacematching";
    }

    @Override
    public NodesSpecifier getNodeRegex() {
      return _nodeRegex;
    }

    @Override
    public void setNodeRegex(NodesSpecifier regex) {
      _nodeRegex = regex;
    }    
  }  
  
  @Override
  protected Answerer createAnswerer(Question question, IBatfish batfish) {
    return new InterfaceMatchingAnswerer(question, batfish);
  }

  @Override
  protected Question createQuestion() {

    return new InterfaceMatchingQuestion(null);
  }
}
