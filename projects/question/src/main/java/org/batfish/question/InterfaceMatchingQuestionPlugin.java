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
      } else {
        double[][] weight = new double[node1._nodeintf.size()][node2._nodeintf.size()];

        for (Ip ip1 : node1._nodeintf.keySet()) {
          int j = 0;
          for (Ip ip2 : node2._nodeintf.keySet()) {
            weight[i][j] = Math.abs(ip1.asLong() - ip2.asLong());
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
      } else {
        double[][] weight_bgp = new double[node1._nodebgp.size()][node2._nodebgp.size()];
        i = 0;
        for (Ip ip1 : node1._nodebgp.keySet()) {
          int j = 0;
          for (Ip ip2 : node2._nodebgp.keySet()) {
            weight_bgp[i][j] = Math.abs(ip1.asLong() - ip2.asLong());
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
