package org.batfish.question;

import static com.google.common.primitives.Ints.max;

import com.apporiented.algorithm.clustering.AverageLinkageStrategy;
import com.apporiented.algorithm.clustering.Cluster;
import com.apporiented.algorithm.clustering.ClusteringAlgorithm;
import com.apporiented.algorithm.clustering.DefaultClusteringAlgorithm;
import com.apporiented.algorithm.clustering.visualization.DendrogramPanel;
import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.auto.service.AutoService;
import java.awt.BorderLayout;
import java.awt.Color;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.WindowConstants;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.Pair;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Edge;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.questions.NodesSpecifier;
import org.batfish.datamodel.questions.Question;
import org.batfish.role.InferRoles;
import org.batfish.role.InferRoles.PreToken;
import org.batfish.role.NodeRoleDimension;

@AutoService(Plugin.class)
public class NewRolesQuestionPlugin extends QuestionPlugin {

  public static class NewRolesAnswerElement extends AnswerElement {

    private static final String PROP_ROLE_DIMENSION = "roleDimension";

    private static final String PROP_ROLE_MAP = "roleMap";

    @Nonnull private NodeRoleDimension _roleDimension;

    @Nonnull private SortedMap<String, SortedSet<String>> _roleMap;

    @JsonCreator
    public NewRolesAnswerElement(
        @JsonProperty(PROP_ROLE_DIMENSION) NodeRoleDimension dimension,
        @JsonProperty(PROP_ROLE_MAP) SortedMap<String, SortedSet<String>> roleMap) {
      _roleDimension = dimension;
      _roleMap = roleMap == null ? new TreeMap<>() : roleMap;
    }

    @JsonProperty(PROP_ROLE_DIMENSION)
    public NodeRoleDimension getRoleDimension() {
      return _roleDimension;
    }

    @JsonProperty(PROP_ROLE_MAP)
    public SortedMap<String, SortedSet<String>> getRoleMap() {
      return _roleMap;
    }
  }

  public static class NewRolesAnswerer extends Answerer {

    public NewRolesAnswerer(Question question, IBatfish batfish) {
      super(question, batfish);
    }

    @Override
    public NewRolesAnswerElement answer() {

      NewRolesQuestion question = (NewRolesQuestion) _question;

      // collect relevant nodes in a list.
      Set<String> nodes = question.getNodeRegex().getMatchingNodes(_batfish);

      // collect relevant border nodes in a list.
      Set<String> borderNodes = question.getBorderNodeRegex().getMatchingNodes(_batfish);

      InferRoles infer = new InferRoles(nodes, _batfish.getEnvironmentTopology(), false);
      List<Pair<Double, NodeRoleDimension>> supportScores = new ArrayList<>();

      infer
          .inferRoles()
          .stream()
          .forEach(
              (nodeRoleDimension) ->
                  supportScores.add(
                      new Pair<>(
                          infer.computeRoleScore(
                              nodeRoleDimension
                                  .getRoleRegexes()
                                  .get(0)), // We consider only the first since its created as -
                          // Collections.singletonList(regex)
                          nodeRoleDimension)));

      SortedMap<Long, SortedSet<String>> possibleBorderRouters =
          inferBorderNodes(borderNodes, question.getAsNumbers());

      NodeRoleDimension roleDimension =
          _batfish
              .getNodeRoleDimension(question.getRoleDimension())
              .orElseThrow(
                  () ->
                      new BatfishException(
                          "No role dimension found for " + question.getRoleDimension()));
      SortedMap<String, SortedSet<String>> defaultRoleNodeMap =
          roleDimension.createRoleNodesMap(nodes);

      if (possibleBorderRouters.size() > 0) {
        List<Set<String>> nodeHierarchy =
            computeNodeDistances(possibleBorderRouters, new HashSet<>(nodes));

        //Selects the best one based on the Linear combination of both Todds and Yuvals Idea.
        double maxSupport = 0;
        for (Pair<Double, NodeRoleDimension> pair : supportScores) {
          double newSupport = computeWeightedSupportScores(pair, nodeHierarchy);
          if (newSupport > maxSupport) {
            roleDimension = pair.getSecond();
            maxSupport = newSupport;
          }
        }
        
        //Modifies the Role->Nodes mapping by Adding the notion of Layer to it.
        SortedMap<String, SortedSet<String>> roleNodesMapByLayer = new TreeMap<>();
        int i = 0;
        for (Set<String> layer : nodeHierarchy) {
          SortedMap<String, SortedSet<String>> roleNodesMap =
              roleDimension.createRoleNodesMap(layer);
          for (String role : roleNodesMap.keySet()) {
            roleNodesMapByLayer.put("Layer " + i + " :" + role, roleNodesMap.get(role));
          }
          i++;
        }
        defaultRoleNodeMap = roleNodesMapByLayer;
      }

      SortedSet<String> sortedNodes = new TreeSet<>(nodes);
      double[][] distanceMatrix = editDistanceComputation(sortedNodes);
      ClusteringAlgorithm alg = new DefaultClusteringAlgorithm();
      Cluster cluster = alg.performClustering(distanceMatrix, sortedNodes.toArray(new String[0]),
          new AverageLinkageStrategy());
      DendrogramPanel dp = new DendrogramPanel();
      dp.setModel(cluster);
      JFrame frame = new JFrame();
      frame.setSize(400, 300);
      frame.setLocation(400, 300);
      frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
      JPanel content = new JPanel();
      frame.setContentPane(content);
      content.setBackground(Color.red);
      content.setLayout(new BorderLayout());
      content.add(dp, BorderLayout.CENTER);
      dp.setBackground(Color.WHITE);
      dp.setLineColor(Color.BLACK);
      dp.setScaleValueDecimals(0);
      dp.setScaleValueInterval(1);
      dp.setShowDistances(false);
      dp.setModel(cluster);
      frame.setVisible(true);
      

      NewRolesAnswerElement answerElement = new NewRolesAnswerElement(roleDimension,
          defaultRoleNodeMap);

      return answerElement;
    }

    /*
    Infer the border Nodes of topology using As numbers if provided else
    use the assumption that in EBGP remote-as is different from local-as.
    The @param borderNodes is the set provided by user.
    This function finally returns the border routers mapped by their remote-as
    */
    private SortedMap<Long, SortedSet<String>> inferBorderNodes(
        Set<String> borderNodes, String asNumbers) {
      Set<Long> asNum =
          asNumbers != null
              ? Arrays.stream(asNumbers.split(",")).map(Long::parseLong).collect(Collectors.toSet())
              : new HashSet<>();
      Map<String, Configuration> configurations = _batfish.loadConfigurations();
      Set<String> copyBorderNodes = new HashSet<>(borderNodes);
      SortedMap<Long, SortedSet<String>> possibleBorderRouters = new TreeMap<>();
      for (Configuration c : configurations.values()) {
        String hostname = c.getHostname();
        for (Vrf vrf : c.getVrfs().values()) {
          BgpProcess proc = vrf.getBgpProcess();
          if (proc != null) {
            for (BgpActivePeerConfig neighbor : proc.getActiveNeighbors().values()) {
              if (Long.compare(neighbor.getRemoteAs(), neighbor.getLocalAs()) != 0
                  & neighbor.getRemoteAs() < 64512
                  & neighbor.getLocalAs() < 64512
                  & (!asNum.contains(neighbor.getRemoteAs()))) {
                SortedSet<String> possible =
                    possibleBorderRouters.computeIfAbsent(
                        neighbor.getRemoteAs(), k -> new TreeSet<>());
                possible.add(hostname);
                copyBorderNodes.remove(hostname);
              }
            }
          }
        }
      }
      if (copyBorderNodes.size() > 0) {
        possibleBorderRouters.put(0L, new TreeSet<>(copyBorderNodes));
      }
      return possibleBorderRouters;
    }

    /*
    Given the set of border routers compute the Hierarchy of Topology.
    The hop count from the "border routers" is defined as the distance
    from one of the border routers and is minimum
     */
    private List<Set<String>> computeNodeDistances(
        SortedMap<Long, SortedSet<String>> borderNodes, Set<String> nodes) {

      Set<String> borderNodesList =
          borderNodes.values().stream().flatMap(SortedSet::stream).collect(Collectors.toSet());
      nodes.removeAll(borderNodesList);

      Set<String> children = computeNextLayerNodes(borderNodesList, nodes);
      List<Set<String>> nodeHierarchy = new ArrayList<>();
      while (children.size() != 0) {
        nodeHierarchy.add(children);
        children = computeNextLayerNodes(children, nodes);
      }
      return nodeHierarchy;
    }

    private Set<String> computeNextLayerNodes(Set<String> parents, Set<String> nodes) {
      Map<String, SortedSet<Edge>> nodeEdges = _batfish.getEnvironmentTopology().getNodeEdges();
      Set<String> nextLayer = new HashSet<>();
      for (String parent : parents) {
        SortedSet<Edge> edges = nodeEdges.get(parent);
        for (Edge e : edges) {
          if (!e.getNode1().equals(parent) & nodes.contains(e.getNode1())) {
            nextLayer.add(e.getNode1());
            nodes.remove(e.getNode1());
          }
        }
      }
      return nextLayer;
    }

    /*
    Given a role partition from Todd's Hypothesis calculate the Edge distance metric and combine
    them using alpha.
    */
    private double computeWeightedSupportScores(
        Pair<Double, NodeRoleDimension> pair, List<Set<String>> nodeHierarchy) {

      SortedMap<String, SortedSet<String>> roleNodesMap =
          pair.getSecond()
              .createRoleNodesMap(
                  nodeHierarchy.stream().flatMap(Set::stream).collect(Collectors.toSet()));
      SortedMap<String, Integer> nodeDistanceMap = new TreeMap<>();
      IntStream.range(0, nodeHierarchy.size())
          .forEach(
              level ->
                  nodeHierarchy
                      .get(level)
                      .forEach(nodeName -> nodeDistanceMap.put(nodeName, level + 1)));

      double supportSum = 0.0;
      for (String role : roleNodesMap.keySet()) {
        SortedSet<String> roleNodes = roleNodesMap.get(role);
        int count = 0;
        for (String node1 : roleNodes) {
          for (String node2 : roleNodes) {
            count += nodeDistanceMap.get(node1).equals(nodeDistanceMap.get(node2)) ? 1 : 0;
          }
        }
        supportSum += (double) count / (roleNodes.size() * roleNodes.size());
      }
      supportSum = supportSum / roleNodesMap.size();
      double alpha =
          (supportSum * supportSum) / (supportSum * supportSum + pair.getFirst() * pair.getFirst());
      return alpha * pair.getFirst() * alpha * pair.getFirst()
          + (1 - alpha) * supportSum * (1 - alpha) * supportSum;
    }

    // Given a set of sorted Nodes compute their Token edit Distance matrix.
    private double[][] editDistanceComputation(SortedSet<String> nodes) {
      SortedMap<String, List<Pair<String, PreToken>>> nameToPreTokensMap = new TreeMap<>();
      nodes.forEach((name) -> nameToPreTokensMap.put(name, InferRoles.pretokenizeName(name)));
      double[][] distances = new double[nodes.size()][nodes.size()];
      int i = 0;
      for (String node1 : nodes) {
        int j = 0;
        for (String node2 : nodes) {
          distances[i][j] =
              node1.equals(node2)
                  ? 0
                  : tokenDistances(nameToPreTokensMap.get(node1), nameToPreTokensMap.get(node2));
          j++;
        }
        i++;
      }
      return distances;
    }

    /*
    Given the list of Tokens for two nodes compute the edit distance between these two nodes.
    Consider only the non-DIGIT+ tokens
    For every token in Node1 find the min edit distance from all the tokens in Node2.
    Normalize it to 1.
    */
    private double tokenDistances(
        List<Pair<String, PreToken>> node1, List<Pair<String, PreToken>> node2) {
      double sum = 0;
      long count =
          Long.max(
              (node1.size()
                  - node1
                      .stream()
                      .filter((pair) -> pair.getSecond().equals(PreToken.DIGIT_PLUS))
                      .count()),
              (node2.size()
                  - node2
                      .stream()
                      .filter((pair) -> pair.getSecond().equals(PreToken.DIGIT_PLUS))
                      .count()));

      for (int i = 0; i < node1.size(); i++) {
        double minimum = 10000;
        if (!node1.get(i).getSecond().equals(PreToken.DIGIT_PLUS)) {
          for (int j = 0; j < node2.size(); j++) {
            if (!node2.get(j).getSecond().equals(PreToken.DIGIT_PLUS)) {
              int editDistance = distance(node1.get(i).getFirst(), node2.get(j).getFirst());
              if (minimum > editDistance) {
                minimum =
                    (double) editDistance
                        / max(node1.get(i).getFirst().length(), node2.get(j).getFirst().length());
              }
            }
          }
          if (minimum != 10000) {
            sum += minimum;
          }
        }
      }
      return sum / count;
    }

    // Edit Distance Algorithm
    private static int distance(String s1, String s2) {
      int edits[][] = new int[s1.length() + 1][s2.length() + 1];
      for (int i = 0; i <= s1.length(); i++) edits[i][0] = i;
      for (int j = 1; j <= s2.length(); j++) edits[0][j] = j;
      for (int i = 1; i <= s1.length(); i++) {
        for (int j = 1; j <= s2.length(); j++) {
          int u = (s1.charAt(i - 1) == s2.charAt(j - 1) ? 0 : 1);
          edits[i][j] =
              Math.min(edits[i - 1][j] + 1, Math.min(edits[i][j - 1] + 1, edits[i - 1][j - 1] + u));
        }
      }
      return edits[s1.length()][s2.length()];
    }
  }

  // <question_page_comment>
  /**
   * List the roles of each node.
   *
   * @type Roles multifile
   * @param nodeRegex Regular expression for names of nodes to include. Default value is '.*' (all
   *     nodes). *
   * @param borderNodeRegex Regular expression for names of border router nodes. Default value is ''
   *     (None).
   * @param roleDimension Which dimension to report on. The default is the primary auto-inferred
   *     one.
   * @param asNumbers The Autonomous System numbers of the given network.
   */
  public static final class NewRolesQuestion extends Question {

    private static final String PROP_NODE_REGEX = "nodeRegex";

    private static final String PROP_ROLE_DIMENSION = "roleDimension";

    private static final String PROP_BORDER_NODE_REGEX = "borderNodeRegex";

    private static final String PROP_AS_NUMBERS = "asNumbers";

    @Nonnull private NodesSpecifier _nodeRegex;
    @Nonnull private NodesSpecifier _borderNodeRegex;

    @Nullable private String _roleDimension;
    @Nullable private String _asNumbers;

    @JsonCreator
    public NewRolesQuestion(
        @JsonProperty(PROP_NODE_REGEX) NodesSpecifier nodeRegex,
        @JsonProperty(PROP_BORDER_NODE_REGEX) NodesSpecifier borderNodeRegex,
        @JsonProperty(PROP_ROLE_DIMENSION) String roleDimension,
        @JsonProperty(PROP_AS_NUMBERS) String asNumbers) {
      _nodeRegex = nodeRegex == null ? NodesSpecifier.ALL : nodeRegex;
      _roleDimension = roleDimension;
      _asNumbers = asNumbers;
      _borderNodeRegex = borderNodeRegex == null ? NodesSpecifier.NONE : borderNodeRegex;
    }

    @Override
    public boolean getDataPlane() {
      return false;
    }

    @Override
    public String getName() {
      return "newroles";
    }

    @JsonProperty(PROP_NODE_REGEX)
    public NodesSpecifier getNodeRegex() {
      return _nodeRegex;
    }

    @JsonProperty(PROP_BORDER_NODE_REGEX)
    public NodesSpecifier getBorderNodeRegex() {
      return _borderNodeRegex;
    }

    @JsonProperty(PROP_ROLE_DIMENSION)
    public String getRoleDimension() {
      return _roleDimension;
    }

    @JsonProperty(PROP_AS_NUMBERS)
    public String getAsNumbers() {
      return _asNumbers;
    }
  }

  @Override
  protected Answerer createAnswerer(Question question, IBatfish batfish) {
    return new NewRolesAnswerer(question, batfish);
  }

  @Override
  protected Question createQuestion() {
    return new NewRolesQuestion(null, null, null, null);
  }
}
