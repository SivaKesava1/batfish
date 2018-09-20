package org.batfish.question;

import static com.google.common.base.MoreObjects.firstNonNull;

import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.auto.service.AutoService;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.lang.Math;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.Map.Entry;
import java.util.NavigableMap;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.common.util.CommonUtil;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Edge;
import org.batfish.datamodel.Interface;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Topology;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.collections.NodeInterfacePair;
import org.batfish.datamodel.questions.INodeRegexQuestion;
import org.batfish.datamodel.questions.NodesSpecifier;
import org.batfish.datamodel.questions.Question;
import org.batfish.role.NodeRoleDimension;

@AutoService(Plugin.class)
public class RoleInterfaceMatchingQuestionPlugin extends QuestionPlugin {

  public static class RoleInterfaceMatchingAnswerElement extends AnswerElement {

    public static final String PROP_ASNS = "asns";

    private String _asns;

    public RoleInterfaceMatchingAnswerElement(@JsonProperty(PROP_ASNS) String asns) {
      _asns = asns;
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

  public static class RoleInterfaceMatchingAnswerer extends Answerer {

    public RoleInterfaceMatchingAnswerer(Question question, IBatfish batfish) {
      super(question, batfish);
    }

    private class NodeData {
      Map<Ip, Entry<String, String>> _nodeintf;

      NodeData(Map<Ip, Entry<String, String>> nodeintf) {
        _nodeintf = new HashMap<>(nodeintf);
      }
    }

    private class Pair {
      String _node1;
      String _node2;
      int _editDistance;
      int[] _intfMap;
      int _intfScore;

      Pair(String node1, String node2, int editDistance, int[] intfMap, int intfScore) {
        _node1 = node1;
        _node2 = node2;
        _editDistance = editDistance;
        _intfMap = intfMap;
        _intfScore = intfScore;
      }
    }

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

    private Map<Ip, Entry<String, String>> interface_name_mapping(
        NavigableMap<String, Interface> interfaces) {
      Map<Ip, Entry<String, String>> actionMap = new HashMap<>();
      for (Entry<String, Interface> e : interfaces.entrySet()) {
        if (e.getValue().getAllAddresses().size() != 0) {
          String name;
          if (!e.getValue().getDeclaredNames().isEmpty()) {
            name = e.getValue().getDeclaredNames().first();
          } else {
            name = e.getValue().getName();
          }

          actionMap.put(
              e.getValue().getAllAddresses().iterator().next().getIp(),
              new AbstractMap.SimpleEntry<>(name, e.getValue().getDescription()));
        }
      }
      return actionMap;
    }

    private Pair IPMapping(NodeData node1, NodeData node2, String node1Name, String node2Name) {

      int editDistance = distance(node1Name, node2Name);

      int[] intfMap = null;
      int intfScore = 0;
      int i = 0;

      if (node1._nodeintf.size() == 0 || node2._nodeintf.size() == 0) {
        intfScore = (int) Math.pow(2, 24);
        intfMap = new int[0];
      } else {

        if (node1._nodeintf.size() < node2._nodeintf.size()) {
          NodeData tmp = node2;
          node2 = node1;
          node1 = tmp;
          String stmp = node2Name;
          node2Name = node1Name;
          node1Name = stmp;
        }
        double[][] weight = new double[node1._nodeintf.size()][node2._nodeintf.size()];
        for (Ip ip1 : node1._nodeintf.keySet()) {
          int j = 0;
          for (Ip ip2 : node2._nodeintf.keySet()) {
            weight[i][j] = Math.abs(ip1.asLong() - ip2.asLong());
            j++;
          }
          i++;
        }

        HungarianAlgorithm intfMatching = new HungarianAlgorithm(weight);
        intfMap = intfMatching.execute();
        for (int k = 0; k < intfMap.length; k++) {
          if (intfMap[k] != -1) {
            intfScore = (int) (intfScore + weight[k][intfMap[k]]);
          }
        }
      }

      return new Pair(node1Name, node2Name, editDistance, intfMap, intfScore);
    }

    private Pair neighborNameMapping(
        LinkedHashMap<String, Set<Interface>> node1Interfaces,
        LinkedHashMap<String, Set<Interface>> node2Interfaces,
        String node1Name,
        String node2Name) {

      int editDistance = distance(node1Name, node2Name);

      int[] intfMap = null;
      int intfScore = 0;
      int i = 0;

      if (node1Interfaces.size() == 0 || node2Interfaces.size() == 0) {
        intfScore = (int) Math.pow(2, 24);
        intfMap = new int[0];
      } else {

        if (node1Interfaces.size() < node2Interfaces.size()) {
          LinkedHashMap<String, Set<Interface>> tmp = node2Interfaces;
          node2Interfaces = node1Interfaces;
          node1Interfaces = tmp;
          String name = node2Name;
          node2Name = node1Name;
          node1Name = name;
        }
        double[][] weight = new double[node1Interfaces.size()][node2Interfaces.size()];

        for (String n1 : node1Interfaces.keySet()) {
          int j = 0;
          for (String n2 : node2Interfaces.keySet()) {
            weight[i][j] = distance(n1, n2);
            j++;
          }
          i++;
        }

        HungarianAlgorithm intfMatching = new HungarianAlgorithm(weight);
        intfMap = intfMatching.execute();
        for (int k = 0; k < intfMap.length; k++) {
          if (intfMap[k] != -1) {
            intfScore = (int) (intfScore + weight[k][intfMap[k]]);
          }
        }
      }

      return new Pair(node1Name, node2Name, editDistance, intfMap, intfScore);
    }

    /*
     * Given a node, its edges and the rolesMap, classify the edges based on to which role
     * these edges connects to. The return type is a mapping from a role to the names of
     * interfaces of the given node which connects to that role.
     */
    private SortedMap<String, Set<String>> sortEdgesByRoles(
        SortedSet<Edge> edges, String node, SortedMap<String, SortedSet<String>> roleNodeMap) {
      SortedMap<String, Set<String>> edgesByRoles = new TreeMap<>();

      for (String s : roleNodeMap.keySet()) {
        edgesByRoles.put(s, new HashSet<>());
      }
      if (edges != null) {
        for (Edge e : edges) {
          NodeInterfacePair first = e.getFirst();
          if (!first.getHostname().equals(node)) {
            for (String s : roleNodeMap.keySet()) {
              if (roleNodeMap.get(s).contains(first.getHostname())) {
                edgesByRoles.get(s).add(e.getInt2());
                break;
              }
            }
          }
        }
      }
      return edgesByRoles;
    }

    private LinkedHashMap<String, Set<Interface>> mapNeighborNamesToInterfaces(
        SortedSet<Edge> edges, Set<Interface> interfaces, String node) {

      LinkedHashMap<String, Set<Interface>> interfacesByNeighborNames = new LinkedHashMap<>();
      if (edges != null) {
        for (Edge e : edges) {
          if (!e.getNode1().equals(node)) {
            for (Interface i : interfaces) {
              if (i.getDeclaredNames().contains(e.getInt2())) {
                if (!interfacesByNeighborNames.containsKey(e.getNode1())) {
                  interfacesByNeighborNames.put(e.getNode1(), new HashSet<>());
                }
                interfacesByNeighborNames.get(e.getNode1()).add(i);
              }
            }
          }
        }
      }
      return interfacesByNeighborNames;
    }

    @Override
    public AnswerElement answer() {
      RoleInterfaceMatchingQuestion question = (RoleInterfaceMatchingQuestion) _question;
      Set<String> includeNodes = question.getNodeRegex().getMatchingNodes(_batfish);
      int algorithm = question.getAlgorithm();
      NodeRoleDimension roleDimension =
          _batfish
              .getNodeRoleDimension(null)
              .orElseThrow(() -> new BatfishException("No role dimension found "));
      SortedMap<String, SortedSet<String>> roleNodeMap =
          roleDimension.createRoleNodesMap(includeNodes);
      String[] nodes = includeNodes.toArray(new String[includeNodes.size()]);
      Map<String, Configuration> configurations = _batfish.loadConfigurations();
      Topology topology = _batfish.getEnvironmentTopology();

      Map<String, NodeData> requiredData = new HashMap<>();
      Map<String, Set<Interface>> nodeInterface = CommonUtil.computeNodeInterfaces(configurations);

      Map<String, SortedSet<Edge>> nodeEdges = topology.getNodeEdges();
      Map<String, SortedMap<String, Set<String>>> nodeEdgesByRoles = new HashMap<>();

      for (Edge e : nodeEdges.get("bd11f1.anderson")) {
        if (e.getNode1().equals("bd11f1.anderson")) {
          System.out.println(e.getNode2());
        }
      }

//      /* For printing the edges*/
//      for (String s : nodeEdges.keySet()) {
//        System.out.println("\n\nNode Name:" + s);
//        for (Edge e : nodeEdges.get(s)) {
//          if (e.getNode1().equals(s))
//            System.out.println(
//                e.getNode1()
//                    + " :  "
//                    + e.getInt1()
//                    + " ----  "
//                    + e.getNode2()
//                    + "  : "
//                    + e.getInt2());
//        }
//      }
//      SortedSet<Edge>  topologyEdges = topology.getEdges();
//      for (Edge e : topologyEdges) {
//          System.out.println(
//              e.getNode1()
//                  + " :  "
//                  + e.getInt1()
//                  + " ----  "
//                  + e.getNode2()
//                  + "  : "
//                  + e.getInt2());
//      }

      Map<String, LinkedHashMap<String, Set<Interface>>> nodeInterfacesByNeighborName =
          new HashMap<>();

      for (String hostname : nodes) {
        Configuration node = configurations.get(hostname);
        NodeData nodedata = new NodeData(interface_name_mapping(node.getAllInterfaces()));
        requiredData.put(hostname, nodedata);
        nodeEdgesByRoles.put(
            hostname, sortEdgesByRoles(nodeEdges.get(hostname), hostname, roleNodeMap));
        nodeInterfacesByNeighborName.put(
            hostname,
            mapNeighborNamesToInterfaces(
                nodeEdges.get(hostname), nodeInterface.get(hostname), hostname));
      }

      List<String> roles = new ArrayList<>(roleNodeMap.keySet());
      StringBuilder sb = new StringBuilder("Results for Interface Matching\n");

      if (algorithm == 3) {
        for (String r : roles) {
          List<String> roleNodes = new ArrayList<>(roleNodeMap.get(r));
          for (int k = 0; k < roleNodes.size(); k++) {
            String node1 = roleNodes.get(k);
            for (int l = k + 1; l < roleNodes.size(); l++) {
              String node2 = roleNodes.get(l);
              Pair rolePair =
                  neighborNameMapping(
                      nodeInterfacesByNeighborName.get(node1),
                      nodeInterfacesByNeighborName.get(node2),
                      node1,
                      node2);
              LinkedHashMap<String, Set<Interface>> node1Interfaces =
                  nodeInterfacesByNeighborName.get(rolePair._node1);
              LinkedHashMap<String, Set<Interface>> node2Interfaces =
                  nodeInterfacesByNeighborName.get(rolePair._node2);
              List<String> node1Neighbors = new ArrayList<>(node1Interfaces.keySet());
              List<String> node2Neighbors = new ArrayList<>(node2Interfaces.keySet());

              sb.append(
                  "\nRouter1: "
                      + rolePair._node1
                      + "\nRouter2: "
                      + rolePair._node2
                      + "\nInterfaceIPScore: "
                      + rolePair._intfScore
                      + "\nNameEditDistance: "
                      + rolePair._editDistance
                      + "\n");

              for (int j = 0; j < rolePair._intfMap.length; j++) {

                sb.append("R1 Neighbor: " + node1Neighbors.get(j) + " -- Interfaces [");

                for (Interface i : node1Interfaces.get(node1Neighbors.get(j))) {
                  sb.append(
                      i.getAddress()
                          + "-"
                          + i.getName()
                          + "-"
                          + i.getDescription()
                          + ",");
                }
                sb.append("]\n");
                if (rolePair._intfMap[j] != -1) {
                  sb.append(
                      "R2 Neighbor: "
                          + node2Neighbors.get(rolePair._intfMap[j])
                          + " -- Interfaces [");

                  for (Interface i :
                      node2Interfaces.get(node2Neighbors.get(rolePair._intfMap[j]))) {
                    sb.append(
                        i.getAddress()
                            + "-"
                            + i.getName()
                            + "-"
                            + i.getDescription()
                            + ",");
                  }
                  sb.append("]\n");
                }
              }
            }
          }
        }
      }

      if (algorithm == 1) {
        for (String r : roles) {
          List<String> roleNodes = new ArrayList<>(roleNodeMap.get(r));
          for (int k = 0; k < roleNodes.size(); k++) {
            String node1 = roleNodes.get(k);
            for (int l = k + 1; l < roleNodes.size(); l++) {
              String node2 = roleNodes.get(l);
              SortedMap<String, Set<String>> node1SortedEdges = nodeEdgesByRoles.get(node1);
              SortedMap<String, Set<String>> node2SortedEdges = nodeEdgesByRoles.get(node2);
              sb.append("\n\nRouter1:" + node1 + "\nRouter2:" + node2);
              for (String s : node1SortedEdges.keySet()) {
                if (node1SortedEdges.get(s).size() + node2SortedEdges.get(s).size() > 0) {
                  sb.append("\n Interface/s Connects to Role: " + s + "\n");
                  Set<Interface> node1Interfaces = nodeInterface.get(node1);
                  Set<Interface> node2Interfaces = nodeInterface.get(node2);

                  sb.append(" R1 interfaces: [");
                  for (String interfaceName : node1SortedEdges.get(s)) {
                    for (Interface i : node1Interfaces) {
                      if (i.getDeclaredNames().contains(interfaceName)) {
                        sb.append(
                            interfaceName
                                + " - "
                                + i.getAddress()
                                + " - "
                                + i.getDescription()
                                + " , ");
                        break;
                      }
                    }
                  }

                  sb.append("]\n R2 interfaces: [");
                  for (String interfaceName : node2SortedEdges.get(s)) {
                    for (Interface i : node2Interfaces) {
                      if (i.getDeclaredNames().contains(interfaceName)) {
                        sb.append(
                            interfaceName
                                + " - "
                                + i.getAddress()
                                + " - "
                                + i.getDescription()
                                + " , ");
                        break;
                      }
                    }
                  }
                  sb.append("]\n");
                }
              }
            }
          }
        }
      }
      if (algorithm == 2) {
        for (int i = 0; i < roles.size(); i++) {
          List<String> roleNodes = new ArrayList<>(roleNodeMap.get(roles.get(i)));
          sb.append(roles.get(i));
          sb.append(roleNodes);
          sb.append("\n");
          for (int k = 0; k < roleNodes.size(); k++) {
            String node1Name = roleNodes.get(k);
            for (int l = k + 1; l < roleNodes.size(); l++) {
              String node2Name = roleNodes.get(l);
              Pair rolePair =
                  IPMapping(
                      requiredData.get(node1Name),
                      requiredData.get(node2Name),
                      node1Name,
                      node2Name);
              Map<Ip, Entry<String, String>> node1 = requiredData.get(rolePair._node1)._nodeintf;
              Map<Ip, Entry<String, String>> node2 = requiredData.get(rolePair._node2)._nodeintf;
              List<Ip> keysN2 = new ArrayList<>(node2.keySet());
              List<Ip> keysN1 = new ArrayList<>(node1.keySet());
              sb.append(
                  "\nRouter1: "
                      + rolePair._node1
                      + "\nRouter2: "
                      + rolePair._node2
                      + "\nInterfaceIPScore: "
                      + rolePair._intfScore
                      + "\nNameEditDistance: "
                      + rolePair._editDistance
                      + "\n");
              for (int j = 0; j < rolePair._intfMap.length; j++) {
                if (rolePair._intfMap[j] != -1) {
                  sb.append(
                      "R1:  ("
                          + keysN1.get(j)
                          + " , "
                          + node1.get(keysN1.get(j))
                          + ")\nR2:  ("
                          + keysN2.get(rolePair._intfMap[j])
                          + " , "
                          + node2.get(keysN2.get(rolePair._intfMap[j]))
                          + ")\n");
                } else {
                  sb.append(
                      "R1:  ("
                          + keysN1.get(j)
                          + " , "
                          + node1.get(keysN1.get(j))
                          + ")\nR2:  None\n");
                }
              }
            }
          }
        }
      }


      return new RoleInterfaceMatchingAnswerElement(sb.toString());
    }
  }

  //  @param-algorithm to choose between
  // 1.Based on Neighbor Role
  // 2.Based on Interface IP Address
  // 3. Based on Neighbor Names Edit Distance

  public static class RoleInterfaceMatchingQuestion extends Question implements INodeRegexQuestion {

    private static final String PROP_NODE_REGEX = "nodeRegex";
    private NodesSpecifier _nodeRegex;
    private static final String PROP_ALGORITHM = "algorithm";
    private int _algorithm;

    public RoleInterfaceMatchingQuestion(
        @JsonProperty(PROP_NODE_REGEX) NodesSpecifier nodeRegex,
        @JsonProperty(PROP_ALGORITHM) int algorithm) {
      _nodeRegex = firstNonNull(nodeRegex, NodesSpecifier.ALL);
      _algorithm = algorithm;
    }

    @Override
    public boolean getDataPlane() {
      return false;
    }

    @Override
    public String getName() {
      return "roleinterfacematching";
    }

    @JsonProperty(PROP_ALGORITHM)
    public int getAlgorithm() {
      return _algorithm;
    }

    public void setAlgorithm(int method) {
      _algorithm = method;
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
    return new RoleInterfaceMatchingAnswerer(question, batfish);
  }

  @Override
  protected Question createQuestion() {

    return new RoleInterfaceMatchingQuestion(null, 1);
  }
}
