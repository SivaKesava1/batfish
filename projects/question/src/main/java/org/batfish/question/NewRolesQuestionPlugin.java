package org.batfish.question;

import static com.google.common.primitives.Ints.max;

import com.apporiented.algorithm.clustering.AverageLinkageStrategy;
import com.apporiented.algorithm.clustering.Cluster;
import com.apporiented.algorithm.clustering.ClusteringAlgorithm;
import com.apporiented.algorithm.clustering.DefaultClusteringAlgorithm;
import com.apporiented.algorithm.clustering.visualization.DendrogramPanel;
import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.databind.JsonNode;
import com.google.auto.service.AutoService;
import java.awt.BorderLayout;
import java.awt.Color;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import javax.annotation.Nonnull;
import javax.swing.JFrame;
import javax.swing.JPanel;
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
import org.batfish.datamodel.collections.NamedStructureEquivalenceSet;
import org.batfish.datamodel.collections.NamedStructureEquivalenceSets;
import org.batfish.datamodel.collections.OutlierSet;
import org.batfish.datamodel.questions.NodesSpecifier;
import org.batfish.datamodel.questions.Question;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.question.OutliersQuestionPlugin.OutliersAnswerElement;
import org.batfish.question.OutliersQuestionPlugin.OutliersQuestion;
import org.batfish.question.UnusedStructuresQuestionPlugin.UnusedStructuresQuestion;
import org.batfish.role.InferRoles;
import org.batfish.role.InferRoles.PreToken;
import org.batfish.role.NodeRoleDimension;
import org.batfish.role.OutliersHypothesis;

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
      int algorithm = question.getAlgorithm();
      SortedMap<Long, SortedSet<String>> possibleBorderRouters =
          inferBorderNodes(borderNodes, question.getAsNumbers());
      // Default output when no Algorithm is specified
      NodeRoleDimension roleDimension =
          _batfish
              .getNodeRoleDimension(question.getRoleDimension())
              .orElseThrow(
                  () ->
                      new BatfishException(
                          "No role dimension found for " + question.getRoleDimension()));

      if (possibleBorderRouters.size() > 0 & algorithm > 0) {

        List<Set<String>> nodeHierarchy =
            computeHopCount(possibleBorderRouters, new HashSet<>(nodes));
        // Selects the best one based on the Linear combination of both Todds and Yuvals Idea.
        if (algorithm == 1) {
          List<Pair<Double, NodeRoleDimension>> supportScores = new ArrayList<>();
          InferRoles infer = new InferRoles(nodes, _batfish.getEnvironmentTopology(), false);
          infer
              .inferRoles()
              .forEach((nodeRoleDimension) -> {
                assert nodeRoleDimension
                    .getRoleRegexes() != null;
                supportScores.add(
                    new Pair<>(
                        infer.computeRoleScore(
                            nodeRoleDimension
                                .getRoleRegexes()
                                .get(0)), // We consider only the first since its created as -
                        // Collections.singletonList(regex)
                        nodeRoleDimension));
              });
          double maxSupport = 0;
          for (Pair<Double, NodeRoleDimension> pair : supportScores) {
            double newSupport = computeAlphaWeightedScore(pair, nodeHierarchy);
            if (newSupport > maxSupport) {
              roleDimension = pair.getSecond();
              maxSupport = newSupport;
            }
          }
        }
        // Hierarchical Clustering based on Min Edit Distances
        if (algorithm == 2) {
          Set<String> collect =
              nodeHierarchy.stream().flatMap(Collection::stream).collect(Collectors.toSet());
          double[][] distanceMatrix = editDistanceComputation(nodeHierarchy);
          ClusteringAlgorithm alg = new DefaultClusteringAlgorithm();
          Cluster cluster =
              alg.performClustering(
                  distanceMatrix,
                  new TreeSet<>(collect).toArray(new String[0]),
                  new AverageLinkageStrategy());
          DendrogramPanel dp = new DendrogramPanel();
          dp.setModel(cluster);
          JFrame frame = new JFrame();
          frame.setSize(400, 300);
          frame.setLocation(400, 300);
          // frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
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
          roleDimension = null;
        }

        if (algorithm == 3 | algorithm == 4) {
          // Modifies the Role->Nodes mapping by Adding the notion of Layer to it.
          Set<String> nodesWithHopCount = new HashSet<>();
          int i = 0;
          for (Set<String> layer : nodeHierarchy) {
            i++;
            for (String node : layer) {
              nodesWithHopCount.add(i + "#" + node);
            }
          }
          if (algorithm == 3) {
            SortedSet<NodeRoleDimension> allHopCountRoleDimensions =
                new InferRoles(nodesWithHopCount, _batfish.getEnvironmentTopology(), false)
                    .inferRoles();
            roleDimension =
                allHopCountRoleDimensions
                    .stream()
                    .filter(rd -> rd.getName().equals("auto0"))
                    .collect(Collectors.toList())
                    .get(0);
            nodes = nodesWithHopCount;
          } else {
            roleDimension = null;
            List<NodeRoleDimension> allHopCountRoleDimensions =
                new ArrayList<>(
                    new InferRoles(nodesWithHopCount, _batfish.getEnvironmentTopology(), false)
                        .inferCommonRoleHypothesis());
            List<NodeRoleDimension> allCommonRoleDimensions =
                new ArrayList<>(
                    new InferRoles(nodes, _batfish.getEnvironmentTopology(), false)
                        .inferCommonRoleHypothesis());
            //
            //            List<SortedMap<String, OutliersAnswerElement>> allPartitioningOutliers =
            //                outliersByPartition(allHopCountRoleDimensions, nodesWithHopCount);
            //
            // allPartitioningOutliers.addAll(outliersByPartition(allCommonRoleDimensions, nodes));
            //            allPartitioningOutliers.addAll(outliersByPartition(null,nodes));

            SortedSet<String> serverSets = new TreeSet<>(question.getServerSets());
            SortedMap<String, Function<Configuration, NavigableSet<String>>> serverSetAccessors =
                new TreeMap<>();
            serverSetAccessors.put("DnsServers", Configuration::getDnsServers);
            serverSetAccessors.put("LoggingServers", Configuration::getLoggingServers);
            serverSetAccessors.put("NtpServers", Configuration::getNtpServers);
            serverSetAccessors.put("SnmpTrapServers", Configuration::getSnmpTrapServers);
            serverSetAccessors.put("TacacsServers", Configuration::getTacacsServers);

            if (serverSets.isEmpty()) {
              serverSets.addAll(serverSetAccessors.keySet());
            }
            for (String serverSet : serverSets) {
              Function<Configuration, NavigableSet<String>> accessorF =
                  serverSetAccessors.get(serverSet);
              if (accessorF != null) {
                System.out.println("\n-------------" + serverSet + "-----------------");
                List<SortedMap<String, Map<NavigableSet<String>, SortedSet<String>>>>
                    allPartitioningClusters =
                        serverClustersByPartition(
                            allHopCountRoleDimensions, nodesWithHopCount, accessorF);
                allPartitioningClusters.addAll(
                    serverClustersByPartition(allCommonRoleDimensions, nodes, accessorF));
                allPartitioningClusters.addAll(serverClustersByPartition(null, nodes, accessorF));
                clusterServerAnalysis(allPartitioningClusters, nodes);
              }
            }
            SortedMap<String, NamedStructureEquivalenceSets<?>> singleRole =
                namedStructuresSingleRole();

            UnusedStructuresQuestion unusedStructuresQ =
                new UnusedStructuresQuestionPlugin().createQuestion();
            TableAnswerElement unusedStructuresAnswer =
                new UnusedStructuresQuestionPlugin()
                    .createAnswerer(unusedStructuresQ, _batfish)
                    .answer();

            removeUnusedDataStructures(singleRole, unusedStructuresAnswer);

            for (Entry<String, NamedStructureEquivalenceSets<?>> namedStructure :
                singleRole.entrySet()) {
              namedStructure.getValue().removeEmptySetsAndClean();
            }

            List<SortedMap<String, SortedSet<String>>> allPartitioningRoleNodeMap =
                new ArrayList<>();
            allHopCountRoleDimensions.forEach(
                (nd) -> allPartitioningRoleNodeMap.add(nd.createRoleNodesMap(nodesWithHopCount)));
            Set<String> finalNodes = nodes;
            allCommonRoleDimensions.forEach(
                (nd) -> allPartitioningRoleNodeMap.add(nd.createRoleNodesMap(finalNodes)));

            namedStructuresAnalysis(singleRole, allPartitioningRoleNodeMap);
          }
        }
      }

      NewRolesAnswerElement answerElement =
          new NewRolesAnswerElement(
              roleDimension,
              roleDimension != null ? roleDimension.createRoleNodesMap(nodes) : null);

      return answerElement;
    }

    private void removeUnusedDataStructures(
        SortedMap<String, NamedStructureEquivalenceSets<?>> singleRole, TableAnswerElement answer) {
      List<Row> rowsList = answer.getRowsList();
      for (Row row : rowsList) {
        JsonNode structType = row.get("structType");
        if (structType.asText().contains("ipv4 access-list")) {
          removeHelper(singleRole, row, "IpAccessList");
        }
        if (structType.asText().contains("ipv6 access-list")) {
          removeHelper(singleRole, row, "Ip6AccessList");
        }
        if (structType.asText().contains("community")) {
          removeHelper(singleRole, row, "CommunityList");
        }
        if (structType.asText().contains("ipv6 prefix-list")) {
          removeHelper(singleRole, row, "Route6FilterList");
        }
      }
    }

    private void removeHelper(
        SortedMap<String, NamedStructureEquivalenceSets<?>> singleRole,
        Row row,
        String dataStructure) {
      Map<String, String> fileNameHostMap =
          _batfish
              .loadParseVendorConfigurationAnswerElement()
              .getFileMap()
              .entrySet()
              .stream()
              .collect(Collectors.toMap(Entry::getValue, Entry::getKey));
      NamedStructureEquivalenceSets<?> equivalenceSets = singleRole.get(dataStructure);
      SortedSet<? extends NamedStructureEquivalenceSet<?>> structName =
          equivalenceSets.getSameNamedStructures().get(row.get("structName").asText());
      String name = fileNameHostMap.get(row.get("filename").asText());
      if (structName != null) {
        structName.forEach(
            v -> {
              if (v.getNodes().contains(name)) {
                SortedSet<String> nodes = new TreeSet<>(v.getNodes());
                nodes.remove(name);
                v.setNodes(nodes);
              }
            });
      }
    }

    private void namedStructuresAnalysis(
        SortedMap<String, NamedStructureEquivalenceSets<?>> singleRole,
        List<SortedMap<String, SortedSet<String>>> allPartitioningRoleNodeMap) {
      singleRole.get("IpAccessLists");
    }

    /*
    Given various partitioning and the nodes this function generates outliers for each role and
    for each partitioning.
    */
    private List<SortedMap<String, OutliersAnswerElement>> outliersByPartition(
        List<NodeRoleDimension> allPartitions, Set<String> nodes) {
      OutliersQuestion innerQ = new OutliersQuestionPlugin().createQuestion();
      innerQ.setNamedStructTypes(new TreeSet<>());
      innerQ.setHypothesis(OutliersHypothesis.SAME_SERVERS);
      //      innerQ.setVerbose(true);
      OutliersQuestionPlugin innerPlugin = new OutliersQuestionPlugin();
      List<SortedMap<String, OutliersAnswerElement>> allPartitioningOutliers = new ArrayList<>();
      if (allPartitions != null) {
        for (NodeRoleDimension partition : allPartitions) {
          /*System.out.print(
          new NewRolesAnswerElement(partition, partition.createRoleNodesMap(nodes))
              .prettyPrint());*/
          SortedMap<String, OutliersAnswerElement> outliersByRoleForAPartitioning = new TreeMap<>();
          SortedMap<String, SortedSet<String>> roleNodesMap = partition.createRoleNodesMap(nodes);
          for (Map.Entry<String, SortedSet<String>> roleNodes : roleNodesMap.entrySet()) {
            innerQ.setNodeRegex(new NodesSpecifier(namesToRegex(roleNodes.getValue())));
            OutliersAnswerElement answer = innerPlugin.createAnswerer(innerQ, _batfish).answer();
            outliersByRoleForAPartitioning.put(roleNodes.getKey(), answer);
            //            if(answer.getServerOutliers().size()>0){
            //              System.out.println("For Role : " + roleNodes.getKey());
            //            }
            //            System.out.print(answer.prettyPrint());
            printHelper(answer, roleNodes.getKey());
          }
          allPartitioningOutliers.add(outliersByRoleForAPartitioning);
          System.out.println("------------------------------------------------------------------");
        }
      } else {
        innerQ.setNodeRegex(new NodesSpecifier(namesToRegex(nodes)));
        OutliersAnswerElement answer = innerPlugin.createAnswerer(innerQ, _batfish).answer();
        System.out.print(answer.prettyPrint());
        // printHelper(answer, "Single Role");
        SortedMap<String, OutliersAnswerElement> outliersByRoleForPartition = new TreeMap<>();
        outliersByRoleForPartition.put("Single Role", answer);
        allPartitioningOutliers.add(outliersByRoleForPartition);
      }
      return allPartitioningOutliers;
    }

    private void printHelper(OutliersAnswerElement answer, String role) {
      if (answer.getServerOutliers().size() > 0) {
        System.out.print("\n/For Role : " + role + ",");
        for (OutlierSet<?> outlier : answer.getServerOutliers()) {
          // System.out.print("  Hypothesis: every node should have the following set of ");
          System.out.print(outlier.getName() + " --");
          System.out.print(
              outlier.getOutliers().size() + "/" + outlier.getConformers().size() + ",");
        }
      }
    }

    private SortedMap<String, StringBuilder> serversAnalysis(
        List<SortedMap<String, OutliersAnswerElement>> allPartitionOutliers,
        Set<String> nodes,
        String server) {

      SortedMap<String, StringBuilder> serverNodeCONMap = new TreeMap<>();
      String initial = new String(new char[allPartitionOutliers.size()]).replace("\0", ",-");
      for (String node : nodes) {
        serverNodeCONMap.put(node, new StringBuilder(initial));
      }

      for (int i = 0; i < allPartitionOutliers.size(); i++) {
        int numberofConformers = 0;
        int numberofOutliers = 0;
        int numberofNI = 0;
        for (Entry<String, OutliersAnswerElement> entry : allPartitionOutliers.get(i).entrySet()) {
          for (OutlierSet<?> outlier : entry.getValue().getServerOutliers()) {
            SortedSet<String> outlierNodes = outlier.getOutliers();
            SortedSet<String> conformers = outlier.getConformers();
            if (outlier.getName().equals(server)) {
              if (conformers.size() >= 0.8 * (conformers.size() + outlierNodes.size())) {
                numberofConformers += conformers.size();
                for (String node : conformers) {
                  serverNodeCONMap.put(
                      node,
                      serverNodeCONMap
                          .getOrDefault(node, new StringBuilder())
                          .replace(i * 2 + 1, i * 2 + 2, "C"));
                }
                if (outlierNodes.size() < 10) {
                  numberofOutliers += outlierNodes.size();
                  for (String node : outlierNodes) {
                    serverNodeCONMap.put(
                        node,
                        serverNodeCONMap
                            .getOrDefault(node, new StringBuilder())
                            .replace(i * 2 + 1, i * 2 + 2, "O"));
                  }
                } else {
                  numberofNI += outlierNodes.size();
                  for (String node : outlierNodes) {
                    serverNodeCONMap.put(
                        node,
                        serverNodeCONMap
                            .getOrDefault(node, new StringBuilder())
                            .replace(i * 2 + 1, i * 2 + 2, "N"));
                  }
                }
              } else {
                numberofNI += outlierNodes.size();
                numberofNI += conformers.size();
                for (String node : conformers) {
                  serverNodeCONMap.put(
                      node,
                      serverNodeCONMap
                          .getOrDefault(node, new StringBuilder())
                          .replace(i * 2 + 1, i * 2 + 2, "N"));
                }
                for (String node : outlierNodes) {
                  serverNodeCONMap.put(
                      node,
                      serverNodeCONMap
                          .getOrDefault(node, new StringBuilder())
                          .replace(i * 2 + 1, i * 2 + 2, "N"));
                }
              }
            }
          }
        }

        //        System.out.print("Partition#  "+(i+1));
        //        System.out.print("Conformers = "+numberofConformers);
        //        System.out.print("Outliers = "+numberofOutliers);
        //        System.out.println("No Information = "+numberofNI);

      }
      //      for (Entry<String, StringBuilder> entry : serverNodeCONMap.entrySet()) {
      //        System.out.println(entry.getKey() + entry.getValue());
      //      }
      return serverNodeCONMap;
    }

    private void serverSuggestions(
        List<Entry<String, Map<String, Map<NavigableSet<String>, SortedSet<String>>>>>
            sortedOutliers,
        Map<String, NavigableSet<String>> outlierNodesDefinition) {

      for (int i = 0; i < sortedOutliers.size(); i++) {
        Entry<String, Map<String, Map<NavigableSet<String>, SortedSet<String>>>> nodePair =
            sortedOutliers.get(i);
        String nodeName = nodePair.getKey();
        Map<NavigableSet<String>, SortedSet<String>> suggestion = new HashMap<>();
        long previous = -1;
        for (Entry<String, Map<NavigableSet<String>, SortedSet<String>>> rolePair :
            nodePair.getValue().entrySet()) {
          String roleName = rolePair.getKey();
          Map<NavigableSet<String>, SortedSet<String>> clusters = rolePair.getValue();
          long roleSize = clusters.values().stream().flatMap(Collection::stream).count();
          if (suggestion.size() == 0) {
            suggestion = rolePair.getValue();
          }
          if (roleSize > 10) {
            previous = previous == -1 ? roleSize : previous;
            if (previous > roleSize) {
              previous = roleSize;
              suggestion = rolePair.getValue();
            }
          }
        }
        System.out.println("Node Name:" + nodeName);
        System.out.println(
            suggestion
                .entrySet()
                .stream()
                .max((s1, s2) -> (s1.getValue().size() > s2.getValue().size() ? 1 : 0))
                .get()
                .getKey());
      }
    }

    // Given the outlier Nodes in a sorted List, for each node for each role it was identified as an
    // outlier suggest the better one using the Set Symmetric Difference or Majority cluster. Then
    // for each suggestion count the number of times it has been suggested.
    private StringBuilder serverSuggestionByRole_BestSelection(
        List<Entry<String, Map<String, Map<NavigableSet<String>, SortedSet<String>>>>>
            sortedOutliers,
        Map<String, NavigableSet<String>> outlierNodesDefinition) {
      StringBuilder outlierRoleSuggestions = new StringBuilder();
      for (Entry<String, Map<String, Map<NavigableSet<String>, SortedSet<String>>>> nodePair :
          sortedOutliers) {
        String nodeName = nodePair.getKey();
        outlierRoleSuggestions.append("\nNode Name:").append(nodeName);
        NavigableSet<String> myDefinition = outlierNodesDefinition.get(nodeName);
        List<NavigableSet<String>> conformerDefinitions = new ArrayList<>();
        for (Entry<String, Map<NavigableSet<String>, SortedSet<String>>> rolePair :
            nodePair.getValue().entrySet()) {
          String roleName = rolePair.getKey();
          // outlierRoleSuggestions.append("\n\t In Role: ").append(roleName);
          Map<NavigableSet<String>, SortedSet<String>> clusters = rolePair.getValue();
          NavigableSet<String> bestClusterConformer = null;
          long roleSize = clusters.values().stream().mapToLong(Collection::size).sum();
          for (Entry<NavigableSet<String>, SortedSet<String>> eachCluster : clusters.entrySet()) {
            if (eachCluster.getValue().contains(nodeName)) {
              // outlierRoleSuggestions.append("\n\t\tIt Has:").append(eachCluster.getKey());
            } else if (eachCluster.getValue().size() > 0.2 * roleSize) {
              // outlierRoleSuggestions.append("\n\t\tOthers Have:").append(eachCluster.getKey());
              if (bestClusterConformer == null) {
                bestClusterConformer = eachCluster.getKey();
              } else {
                //                if (Sets.symmetricDifference(myDefinition,
                // eachCluster.getKey()).size()
                //                    > Sets.symmetricDifference(myDefinition,
                // bestClusterConformer).size()) {
                //                  bestClusterConformer = eachCluster.getKey();
                //                }
                if (eachCluster.getValue().size() > clusters.get(bestClusterConformer).size()) {
                  bestClusterConformer = eachCluster.getKey();
                }
              }
            }
          }
          conformerDefinitions.add(bestClusterConformer);
        }
        // System.out.println("\nNode Name: " + nodeName);
        outlierRoleSuggestions.append("\n\t\tDefinition Present :").append(myDefinition);
        for (NavigableSet<String> each : new HashSet<>(conformerDefinitions)) {
          outlierRoleSuggestions
              .append("\n\t\tSuggestions : ")
              .append(each)
              .append("-")
              .append(Collections.frequency(conformerDefinitions, each));
        }
      }
      return outlierRoleSuggestions;
    }

    // Given the clusters generate the CON map for each router and statistics for each role.
    private void clusterServerAnalysis(
        List<SortedMap<String, Map<NavigableSet<String>, SortedSet<String>>>>
            allPartitioningClusters,
        Set<String> nodes) {
      StringBuilder percentageString = new StringBuilder();
      SortedMap<String, StringBuilder> serverNodeCONMap = new TreeMap<>();
      String initial = new String(new char[allPartitioningClusters.size()]).replace("\0", ",-");
      for (String node : nodes) {
        serverNodeCONMap.put(node, new StringBuilder(initial));
      }
      Map<String, Map<String, Map<NavigableSet<String>, SortedSet<String>>>>
          outlierNodesAndClusters = new HashMap<>();
      Map<String, NavigableSet<String>> outlierNodesDefinition = new HashMap<>();
      for (int i = 0; i < allPartitioningClusters.size(); i++) {
        SortedMap<String, Map<NavigableSet<String>, SortedSet<String>>> clustersByRole =
            allPartitioningClusters.get(i);
        for (Entry<String, Map<NavigableSet<String>, SortedSet<String>>> role :
            clustersByRole.entrySet()) {
          long roleSize = role.getValue().values().stream().mapToLong(Collection::size).sum();
          List<String> clusterSizes = new ArrayList<>();
          int conformers = 0;
          int outliers = 0;
          int ni = 0;
          for (Entry<NavigableSet<String>, SortedSet<String>> cluster :
              role.getValue().entrySet()) {
            NavigableSet<String> key = cluster.getKey();
            int clusterSize = cluster.getValue().size();
            if (key.size() > 0) {
              clusterSizes.add(String.format("%.03f", (double) clusterSize / roleSize) + ",1");
            } else {
              clusterSizes.add(String.format("%.03f", (double) clusterSize / roleSize) + ",0");
            }
            String clusterGroup;
            if (clusterSize > 0.2 * roleSize) {
              clusterGroup = "C";
              conformers += clusterSize;
            } else if (clusterSize < 10) {
              clusterGroup = "O";
              outliers += clusterSize;
              for (String node : cluster.getValue()) {
                Map<String, Map<NavigableSet<String>, SortedSet<String>>> outlierRoleMap =
                    outlierNodesAndClusters.getOrDefault(node, new HashMap<>());
                outlierRoleMap.put(role.getKey(), role.getValue());
                outlierNodesAndClusters.put(node, outlierRoleMap);
                outlierNodesDefinition.putIfAbsent(node, key);
              }
            } else {
              clusterGroup = "N";
              ni += clusterSize;
            }
            for (String node : cluster.getValue()) {
              serverNodeCONMap.put(
                  node,
                  serverNodeCONMap
                      .getOrDefault(node, new StringBuilder())
                      .replace(i * 2 + 1, i * 2 + 2, clusterGroup));
            }
          }
          if (conformers != roleSize) {
            percentageString.append("\nRole: ").append(role.getKey());
            percentageString.append(",").append(roleSize);
            percentageString
                .append(",")
                .append(conformers)
                .append(",")
                .append(outliers)
                .append(",")
                .append(ni);
            clusterSizes.sort(Comparator.reverseOrder());
            clusterSizes.forEach(size -> percentageString.append(",").append(size));
          }
        }
      }
      StringBuilder CONString = new StringBuilder();
      for (Entry<String, StringBuilder> entry : serverNodeCONMap.entrySet()) {
        if (entry.getValue().toString().contains("O")) {
          CONString.append(entry.getKey()).append(entry.getValue()).append("\n");
        }
      }
      List<Entry<String, Map<String, Map<NavigableSet<String>, SortedSet<String>>>>>
          sortedOutliers =
              outlierNodesAndClusters
                  .entrySet()
                  .stream()
                  .sorted(Comparator.comparingInt(o -> -o.getValue().entrySet().size()))
                  .collect(Collectors.toList());
      // serverSuggestions(sortedOutliers,outlierNodesDefinition);
      // System.out.println(serverSuggestionByRole_BestSelection(sortedOutliers,outlierNodesDefinition));
      //      System.out.println(percentageString);
      //      System.out.println(CONString);

    }

    // Helper to the serverClustersByPartition function.
    private Map<NavigableSet<String>, SortedSet<String>> getServerEqSets(
        Function<Configuration, NavigableSet<String>> accessor, SortedSet<String> nodes) {

      Map<NavigableSet<String>, SortedSet<String>> equivSets = new HashMap<>();
      for (String node : nodes) {
        NavigableSet<String> definition =
            accessor.apply(
                _batfish.loadConfigurations().get(node.contains("#") ? node.substring(2) : node));
        SortedSet<String> matchingNodes = equivSets.getOrDefault(definition, new TreeSet<>());
        matchingNodes.add(node.contains("#") ? node.substring(2) : node);
        equivSets.put(definition, matchingNodes);
      }
      return equivSets;
    }
    /*
    Given various partitioning and the nodes this function generates clusters for each role for the
    given accessor which can be getDNSServers or getLoggingServers, and so on.
     */
    private List<SortedMap<String, Map<NavigableSet<String>, SortedSet<String>>>>
        serverClustersByPartition(
            List<NodeRoleDimension> allPartitions,
            Set<String> nodes,
            Function<Configuration, NavigableSet<String>> accessor) {
      List<SortedMap<String, Map<NavigableSet<String>, SortedSet<String>>>>
          allPartitioningClusters = new ArrayList<>();
      if (allPartitions != null) {
        for (NodeRoleDimension partition : allPartitions) {
          SortedMap<String, Map<NavigableSet<String>, SortedSet<String>>>
              clustersByRoleForAPartitioning = new TreeMap<>();
          SortedMap<String, SortedSet<String>> roleNodesMap = partition.createRoleNodesMap(nodes);
          for (Map.Entry<String, SortedSet<String>> roleNodes : roleNodesMap.entrySet()) {
            clustersByRoleForAPartitioning.put(
                roleNodes.getKey(), getServerEqSets(accessor, roleNodes.getValue()));
          }
          allPartitioningClusters.add(clustersByRoleForAPartitioning);
        }
      } else {
        SortedMap<String, Map<NavigableSet<String>, SortedSet<String>>> singleRole =
            new TreeMap<>();
        singleRole.put("Single Role", getServerEqSets(accessor, new TreeSet<>(nodes)));
        allPartitioningClusters.add(singleRole);
      }
      return allPartitioningClusters;
    }

    private SortedMap<String, NamedStructureEquivalenceSets<?>> namedStructuresSingleRole() {
      CompareSameNameQuestionPlugin.CompareSameNameQuestion inner =
          new CompareSameNameQuestionPlugin.CompareSameNameQuestion(
              null, new TreeSet<>(), null, null, null, true);
      CompareSameNameQuestionPlugin.CompareSameNameAnswerer innerAnswerer =
          new CompareSameNameQuestionPlugin().createAnswerer(inner, _batfish);
      CompareSameNameQuestionPlugin.CompareSameNameAnswerElement innerAnswer =
          innerAnswerer.answer();
      return innerAnswer.getEquivalenceSets();
    }

    /* create a regex that matches exactly the given set of names.
    If the names have the hop count included removes it and generates the regex. */
    private String namesToRegex(Set<String> names) {
      names =
          names
              .stream()
              .map((v) -> v.contains("#") ? v.substring(2) : v)
              .collect(Collectors.toSet());
      return names.stream().map(Pattern::quote).collect(Collectors.joining("|"));
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
              if (neighbor.getRemoteAs() != null & neighbor.getLocalAs() != null) {
                if (!neighbor.getRemoteAs().equals(neighbor.getLocalAs())
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
      }
      if (copyBorderNodes.size() > 0) {
        possibleBorderRouters.put(0L, new TreeSet<>(copyBorderNodes));
      }
      return possibleBorderRouters;
    }

    /*
    Given the set of border routers compute the Hierarchy of nodes.
    The hop count from the "border routers" is defined as the distance
    from one of the border routers and is minimum.
     */
    private List<Set<String>> computeHopCount(
        SortedMap<Long, SortedSet<String>> borderNodes, Set<String> nodes) {

      Set<String> borderNodesList =
          borderNodes.values().stream().flatMap(SortedSet::stream).collect(Collectors.toSet());
      nodes.removeAll(borderNodesList);

      Set<String> children = computeNextLayerNodes(borderNodesList, nodes);
      List<Set<String>> nodeHierarchy = new ArrayList<>();
      nodeHierarchy.add(borderNodesList);
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
        if (edges != null) {
          for (Edge e : edges) {
            //Don't consider if its a management interface.
            if (!e.getInt1().contains("Management")
                & !e.getInt2().contains("Management")
                & !e.getInt1().contains("fxp")
                & !e.getInt2().contains("fxp")) {
              if (!e.getNode1().equals(parent) & nodes.contains(e.getNode1())) {
                nextLayer.add(e.getNode1());
                nodes.remove(e.getNode1());
              }
            }
          }
        }
      }
      return nextLayer;
    }

    /*
    Given a role partition from Todd's Hypothesis calculate the Edge distance metric and combine
    them using alpha.
    */
    private double computeAlphaWeightedScore(
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
                      .forEach(nodeName -> nodeDistanceMap.put(nodeName, level)));

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
    private double[][] editDistanceComputation(List<Set<String>> nodeHierarchy) {

      SortedMap<String, Integer> nodeDistanceMap = new TreeMap<>();
      IntStream.range(0, nodeHierarchy.size())
          .forEach(
              level ->
                  nodeHierarchy
                      .get(level)
                      .forEach(nodeName -> nodeDistanceMap.put(nodeName, level)));

      SortedMap<String, List<Pair<String, PreToken>>> nameToPreTokensMap = new TreeMap<>();
      SortedSet<String> nodes = (SortedSet<String>) nodeDistanceMap.keySet();
      nodes.forEach((name) -> nameToPreTokensMap.put(name, InferRoles.pretokenizeName(name)));
      double[][] distances = new double[nodes.size()][nodes.size()];
      int i = 0;
      for (String node1 : nodes) {
        int j = 0;
        for (String node2 : nodes) {
          distances[i][j] =
              node1.equals(node2)
                  ? 0
                  : nodeDistanceMap.get(node1).equals(nodeDistanceMap.get(node2))
                      ? tokenDistances(nameToPreTokensMap.get(node1), nameToPreTokensMap.get(node2))
                      : 1.1;
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

      for (Pair<String, PreToken> aNode1 : node1) {
        double minimum = 10000;
        if (!aNode1.getSecond().equals(PreToken.DIGIT_PLUS)) {
          for (Pair<String, PreToken> aNode2 : node2) {
            if (!aNode2.getSecond().equals(PreToken.DIGIT_PLUS)) {
              int editDistance = distance(aNode1.getFirst(), aNode2.getFirst());
              if (minimum > editDistance) {
                minimum = (double) editDistance / max(aNode1.getFirst().length(),
                    aNode2.getFirst().length());
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
   * @param algorithm The algorithm that should be used to infer Roles. 1 - Linear Combination of
   *     name and Hop count distances. 2 - Hierarchical Clustering Based on Min Edit Distances. 3 -
   *     First by Hop Count and then by Name partitioning. 4 - Outliers.g 0 - Default Todd's best
   *     one.
   * @param serverSets Set of server-set names to analyze drawn from ( DnsServers, LoggingServers, *
   *     NtpServers, SnmpTrapServers, TacacsServers) Default value is '[]' (which denotes all *
   *     server-set names).
   */
  public static final class NewRolesQuestion extends Question {

    private static final String PROP_NODE_REGEX = "nodeRegex";

    private static final String PROP_ROLE_DIMENSION = "roleDimension";

    private static final String PROP_BORDER_NODE_REGEX = "borderNodeRegex";

    private static final String PROP_AS_NUMBERS = "asNumbers";

    private static final String PROP_ALGORITHM = "algorithm";

    private static final String PROP_SERVER_SETS = "serverSets";

    private int _algorithm;
    @Nonnull private NodesSpecifier _nodeRegex;
    @Nonnull private NodesSpecifier _borderNodeRegex;
    private String _roleDimension;
    private String _asNumbers;
    private SortedSet<String> _serverSets;

    @JsonCreator
    public NewRolesQuestion(
        @JsonProperty(PROP_NODE_REGEX) NodesSpecifier nodeRegex,
        @JsonProperty(PROP_BORDER_NODE_REGEX) NodesSpecifier borderNodeRegex,
        @JsonProperty(PROP_ROLE_DIMENSION) String roleDimension,
        @JsonProperty(PROP_AS_NUMBERS) String asNumbers,
        @JsonProperty(PROP_ALGORITHM) int algorithm,
        @JsonProperty(PROP_SERVER_SETS) SortedSet<String> serverSets) {
      _nodeRegex = nodeRegex == null ? NodesSpecifier.ALL : nodeRegex;
      _roleDimension = roleDimension;
      _asNumbers = asNumbers;
      _borderNodeRegex = borderNodeRegex == null ? NodesSpecifier.NONE : borderNodeRegex;
      _algorithm = algorithm;
      _serverSets = serverSets == null ? new TreeSet<>() : serverSets;
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

    @JsonProperty(PROP_ALGORITHM)
    public int getAlgorithm() {
      return _algorithm;
    }

    @JsonProperty(PROP_SERVER_SETS)
    public SortedSet<String> getServerSets() {
      return _serverSets;
    }
  }

  @Override
  protected Answerer createAnswerer(Question question, IBatfish batfish) {
    return new NewRolesAnswerer(question, batfish);
  }

  @Override
  protected Question createQuestion() {
    return new NewRolesQuestion(null, null, null, null, 0, null);
  }
}
