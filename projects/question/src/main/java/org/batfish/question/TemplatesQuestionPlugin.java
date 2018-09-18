package org.batfish.question;

import static org.batfish.role.InferRoles.pretokenizeName;

import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.auto.service.AutoService;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.Pair;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.IpAccessList;
import org.batfish.datamodel.IpAccessListLine;
import org.batfish.datamodel.LineAction;
import org.batfish.datamodel.acl.TrueExpr;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.collections.NamedStructureEquivalenceSet;
import org.batfish.datamodel.collections.NamedStructureEquivalenceSets;
import org.batfish.datamodel.questions.NodesSpecifier;
import org.batfish.datamodel.questions.Question;
import org.batfish.role.InferRoles.PreToken;

@AutoService(Plugin.class)
public class TemplatesQuestionPlugin extends QuestionPlugin {

  private static final double TOKEN_ABSOLUTE_THRESHOLD = 2;
  private static final double TOKEN_RELATIVE_THRESHOLD = 0.2;
  public static class TemplateAnswerElement extends AnswerElement {
    private static final String PROP_TEMPLATE_MAP = "templateMap";
    private SortedMap<StringBuilder, SortedSet<String>> _templateMap;

    public TemplateAnswerElement() {
      _templateMap = new TreeMap<>();
    }

    @JsonProperty(PROP_TEMPLATE_MAP)
    public SortedMap<StringBuilder, SortedSet<String>> getTemplateMap() {
      return _templateMap;
    }

    @Override
    public String prettyPrint() {
      if (_templateMap.size() == 0) {
        return "";
      }
      StringBuilder sb = new StringBuilder("Results for templates\n");
      return sb.toString();
    }
  }

  public static class TemplateAnswerer extends Answerer {

    public TemplateAnswerer(Question question, IBatfish batfish) {
      super(question, batfish);
    }


    @Override
    public TemplateAnswerElement answer() {
      TemplatesQuestion question = (TemplatesQuestion) _question;
      TemplateAnswerElement answerElement = new TemplateAnswerElement();

      // collect relevant nodes in a list.
      Set<String> nodes = question.getNodeRegex().getMatchingNodes(_batfish);

      CompareSameNameQuestionPlugin.CompareSameNameQuestion inner =
          new CompareSameNameQuestionPlugin.CompareSameNameQuestion(
              null, new TreeSet<>(), null, null, question.getNodeRegex(), true);
      CompareSameNameQuestionPlugin.CompareSameNameAnswerer innerAnswerer =
          new CompareSameNameQuestionPlugin().createAnswerer(inner, _batfish);
      CompareSameNameQuestionPlugin.CompareSameNameAnswerElement innerAnswer =
          innerAnswerer.answer();
      SortedMap<String, NamedStructureEquivalenceSets<?>> equivalenceSets =
          innerAnswer.getEquivalenceSets();

      NamedStructureEquivalenceSets<?> dataStructureEquivalenceSets =
          equivalenceSets.get("IpAccessList");
      Set<String> strings = dataStructureEquivalenceSets.getSameNamedStructures().keySet();

      // basedOnBitVectors(dataStructureEquivalenceSets);
      SortedMap<String, List<String>> tokenMap = new TreeMap<>();
      SortedMap<Integer, SortedSet<String>> countTokenMap = new TreeMap<>(Comparator.reverseOrder());
      strings.forEach(
          v -> {
            List<String> tokens =
                pretokenizeName(v).stream().map(Pair::getFirst).collect(Collectors.toList());
            tokenMap.put(v, tokens);
            SortedSet<String> aclSet = countTokenMap.getOrDefault(tokens.size(), new TreeSet<>());
            aclSet.add(v);
            countTokenMap.put(tokens.size(), aclSet);
          });
     getBitVectorMap(dataStructureEquivalenceSets,false,"voip_[a-z]*_out_[0-9]*");
//     basedOnNames();
      return answerElement;
    }

    private <T> SortedMap<String, Set<String>> getBitVectorMap(
        NamedStructureEquivalenceSets<T> dataStructureEquivalenceSets, boolean singleDefinition, String regex) {
      SortedMap<String, Set<String>> bitVectorMap = new TreeMap<>();
      SortedMap<String, SortedSet<String>> bitVectorNodesMap = new TreeMap<>();
      SortedMap<String,Set<String>> pdSequenceMap = new TreeMap<>();
      SortedMap<String,SortedSet<String>> pdSequenceNodesMap = new TreeMap<>();

      Pattern p = Pattern.compile(regex, 0);
      dataStructureEquivalenceSets
          .getSameNamedStructures()
          .forEach(
              (key, value) -> {
                if (p.matcher(key).matches()) {
                  if (!(singleDefinition & value.size() > 1)) {
                    value.forEach(
                        v -> {
                          IpAccessList namedStructure = (IpAccessList) v.getNamedStructure();
                          List<IpAccessListLine> lines = namedStructure.getLines();
                          StringBuilder sb = new StringBuilder();
                          StringBuilder pdBuilder = new StringBuilder();
                          pdBuilder.append("$");
                          lines.forEach(
                              x -> {
                                if (x.getAction().equals(LineAction.PERMIT)) {
                                  sb.append("1");
                                  if (pdBuilder.lastIndexOf("P") != pdBuilder.length() - 1) {
                                    pdBuilder.append("P");
                                  }
                                } else {
                                  sb.append("0");
                                  if (pdBuilder.lastIndexOf("D") != pdBuilder.length() - 1) {
                                    pdBuilder.append("D");
                                  }
                                }
                              });
                          Set<String> sameBitStructures =
                              bitVectorMap.getOrDefault(sb.toString(), new HashSet<>());
                          sameBitStructures.add(key);
                          bitVectorMap.put(sb.toString(), sameBitStructures);

                          Set<String> samePDStructures =
                              pdSequenceMap.getOrDefault(pdBuilder.toString(), new HashSet<>());
                          samePDStructures.add(key);
                          pdSequenceMap.put(pdBuilder.toString(), samePDStructures);

                          SortedSet<String> sameBitNodes =
                              bitVectorNodesMap.getOrDefault(sb.toString(), new TreeSet<>());
                          sameBitNodes.addAll(v.getNodes());
                          bitVectorNodesMap.put(sb.toString(), sameBitNodes);

                          SortedSet<String> samePDStructuresNodes =
                              pdSequenceNodesMap.getOrDefault(
                                  pdBuilder.toString(), new TreeSet<>());
                          samePDStructuresNodes.addAll(v.getNodes());
                          pdSequenceNodesMap.put(pdBuilder.toString(), samePDStructuresNodes);
                        });
                  }
                }
              });
      //pdSequenceMap.forEach((key, value) -> System.out.println(key+"$"+pdSequenceNodesMap.get(key).size()));
      //bitVectorMap.forEach((key, value) -> System.out.println(key+"$"+bitVectorNodesMap.get(key).size()));
      //ACLPrinting(bitVectorMap, dataStructureEquivalenceSets.getSameNamedStructures());


      return bitVectorMap;
    }

    private <T> void ACLPrinting(
        SortedMap<String, Set<String>> bitVectorMap,
        SortedMap<String, SortedSet<NamedStructureEquivalenceSet<T>>> sameNamedStructures) {
      bitVectorMap.forEach(
          (key, value) ->
              value.forEach(
                  acl -> {
                    System.out.println("\n------ACL Name:  " + acl);
                    SortedSet<NamedStructureEquivalenceSet<T>> namedStructureEquivalenceSets =
                        sameNamedStructures.get(acl);
                    namedStructureEquivalenceSets.forEach(
                        v -> {
                          System.out.println("***Definition***");
                          IpAccessList namedStructure = (IpAccessList) v.getNamedStructure();
                          List<IpAccessListLine> lines = namedStructure.getLines();
                          lines.forEach(line -> System.out.println(line.getName()));
                        });
                  }));
    }

    private void basedOnBitVectors(NamedStructureEquivalenceSets<?> dataStructureEquivalenceSets) {
      SortedMap<String, Set<String>> bitVectorMap = new TreeMap<>();
      SortedMap<String, List<IpAccessListLine>> aclDefinitions = new TreeMap<>();
      dataStructureEquivalenceSets
          .getSameNamedStructures()
          .forEach(
              (key, value) -> {
                if (value.size() == 1) {
                  // System.out.println(key + "$" + value.first().getNodes());
                  IpAccessList namedStructure = (IpAccessList) value.first().getNamedStructure();
                  List<IpAccessListLine> lines = namedStructure.getLines();
                  aclDefinitions.put(key, lines);
                  StringBuilder sb = new StringBuilder();
                  lines.forEach(
                      x -> {
                        if (x.getAction().equals(LineAction.PERMIT)) {
                          sb.append("1");
                        } else {
                          sb.append("0");
                        }
                      });
                  Set<String> sameBitStructures =
                      bitVectorMap.getOrDefault(sb.toString(), new HashSet<>());
                  sameBitStructures.add(key);
                  bitVectorMap.put(sb.toString(), sameBitStructures);
                }
              });
      // bitVectorMap.forEach((key, value) -> System.out.println(key+"$"+value));
      Set<String> dataStructuresForTemplating =
          bitVectorMap
              .values()
              .stream()
              .max(Comparator.comparingInt(Collection::size))
              .orElseThrow(
                  () -> new BatfishException("Unable to retrieve the maximum sized IpAccessList"));

      SortedMap<String, List<String>> tokenMap = new TreeMap<>();
      dataStructuresForTemplating.forEach(
          v ->
              tokenMap.put(
                  v, pretokenizeName(v).stream().map(Pair::getFirst).collect(Collectors.toList())));

      List<String> longestNamedStructure =
          tokenMap
              .values()
              .stream()
              .max(Comparator.comparing(Collection::size))
              .orElseThrow(
                  () -> new BatfishException("Unable to retrieve the maximum sized tokenize List"));
//       List<String> template = new ArrayList<>(longestNamedStructure);
//       SortedMap<String,Set<String>> parameters = new TreeMap<>();
//       for (List<String> tokens : tokenMap.values()) {
//         int lastRetrieved = -1;
//         for (int i = 0; i < tokens.size(); i++) {
//           int current = template.indexOf(tokens.get(i));
//           if (lastRetrieved == -1) {
//             if (current > 0) {
//
//             }
//           }
//           lastRetrieved = current;
//         }
//       }
      int numberOfLines = aclDefinitions.get(dataStructuresForTemplating.iterator().next()).size();
      List<IpAccessListLine> template =
          new ArrayList<>(aclDefinitions.get(dataStructuresForTemplating.iterator().next()));
      for (int i = 0; i < numberOfLines; i++) {
        for (String node : dataStructuresForTemplating) {
          IpAccessListLine ipAccessListLine = aclDefinitions.get(node).get(i);
        }
      }
    }

    private  void basedOnNames(){
      SortedMap<String, Configuration> configurations = _batfish.loadConfigurations();
      SortedMap<String, Set<ACLData>> countMap = new TreeMap<>();
      for (Map.Entry<String, Configuration> c : configurations.entrySet()) {
        String nodeName = c.getKey();
        SortedMap<String, Integer> aclTypeMapFromInterfaces = new TreeMap<>();
        c.getValue()
            .getAllInterfaces()
            .values()
            .forEach(
                (intf) -> {
                  if (intf.getIncomingFilter() != null) {
                    if (aclTypeMapFromInterfaces.getOrDefault(intf.getIncomingFilterName(), 0)
                        != 0) {
                      System.out.println("conflict in Input vs output filter category");
                    }
                    aclTypeMapFromInterfaces.put(intf.getIncomingFilterName(), 0);
                  }
                  if (intf.getInboundFilterName() != null) {
                    if (aclTypeMapFromInterfaces.getOrDefault(intf.getInboundFilterName(), 0)
                        != 0) {
                      System.out.println("conflict in Input vs output filter category");
                    }
                    aclTypeMapFromInterfaces.put(intf.getInboundFilterName(), 0);
                  }
                  if (intf.getOutgoingFilterName() != null) {
                    if (aclTypeMapFromInterfaces.getOrDefault(intf.getOutgoingFilterName(), 1)
                        != 1) {
                      System.out.println("conflict in Input vs output filter category");
                    }
                    aclTypeMapFromInterfaces.put(intf.getOutgoingFilterName(), 1);
                  }
                });
        c.getValue()
            .getIpAccessLists()
            .forEach(
                (name, acl) -> {
                  ACLData aclData =
                      new ACLData(
                          nodeName,
                          aclTypeMapFromInterfaces.getOrDefault(name, 2),
                          pretokenizeName(name),
                          acl);
                  String key =
                      Integer.toString(aclData._nameTokens.size())
                          + "#"
                          + Integer.toString(aclTypeMapFromInterfaces.getOrDefault(name, 2));
                  Set<ACLData> acls = countMap.getOrDefault(key, new HashSet<>());
                  acls.add(aclData);
                  countMap.put(key, acls);
                });
      }
      for (Set<ACLData> sameTokenSet : countMap.values()) {
        while (sameTokenSet.size() > 0) {
          ACLData pickedOne = sameTokenSet.iterator().next();
          Set<ACLData> aclTemplateSet = new HashSet<>();
          aclTemplateSet.add(pickedOne);
          for (ACLData anACL : sameTokenSet) {
            addCompatibleACL(pickedOne, anACL, aclTemplateSet);
          }
          if (aclTemplateSet.size() > 1) {
            generateTemplate(aclTemplateSet);
          }
          sameTokenSet.removeAll(aclTemplateSet);
        }
      }
      System.out.println("hello");
    }

    private void generateTemplate(Set<ACLData> aclTemplateSet) {

      ACLData largestACL =
          aclTemplateSet
              .stream()
              .max(Comparator.comparingInt(value -> value.get_acl().getLines().size()))
              .orElseThrow(() -> new BatfishException("Unable to get the Largest ACL"));

      List<IpAccessListLine> linesTemplate = new ArrayList<>(largestACL.get_acl().getLines());
      List<String> nameTemplate = largestACL.getNameTokens()
          .stream()
          .map(Pair::getFirst)
          .collect(Collectors.toList());

      List<ACLData> sortedACLs =
          aclTemplateSet
              .stream()
              .sorted(
                  (v, l) -> v.get_acl().getLines().size() >= l.get_acl().getLines().size() ? 0 : 1)
              .collect(Collectors.toList());
      SortedMap<String, SortedMap<String, String>> parameterMap = new TreeMap<>();
      int parameterCount = 0;

      for (ACLData acl : sortedACLs) {
        List<String> nameTokens =
            acl.getNameTokens().stream().map(Pair::getFirst).collect(Collectors.toList());
        for (int i = 0; i < nameTokens.size(); i++) {
          if (!nameTokens.get(i).equals(nameTemplate.get(i))) {
            if (nameTemplate.get(i).contains("#P")) {
              SortedMap<String, String> nodeParameterMap =
                  parameterMap.getOrDefault(nameTemplate.get(i), new TreeMap<>());
              nodeParameterMap.put(acl.get_nodeName(), nameTokens.get(i));
              parameterMap.put(nameTemplate.get(i), nodeParameterMap);
            } else {
              SortedMap<String, String> nodeParameterMap = new TreeMap<>();
              nodeParameterMap.put(acl.get_nodeName(), nameTokens.get(i));
              nodeParameterMap.put(largestACL.get_nodeName(), nameTemplate.get(i));
              parameterCount += 1;
              nameTemplate.set(i, "#P" + Integer.toString(parameterCount) + "#");
              parameterMap.put("#P" + Integer.toString(parameterCount) + "#", nodeParameterMap);
            }
          }
        }


      }
      System.out.println(nameTemplate);
    }

    private void addCompatibleACL(ACLData pickedOne, ACLData anACL, Set<ACLData> aclTemplateSet) {
      Set<String> nodeNames =
          aclTemplateSet.stream().map(ACLData::get_nodeName).collect(Collectors.toSet());
      int tokenDiff = tokenDifference(pickedOne._nameTokens, anACL._nameTokens);
      if (tokenDiff <= TOKEN_ABSOLUTE_THRESHOLD
          & (double) tokenDiff / pickedOne.getNameTokens().size() <= TOKEN_RELATIVE_THRESHOLD) {
        if (!nodeNames.contains(anACL.get_nodeName())) {
          aclTemplateSet.add(anACL);
        } else {
          ACLData aclData =
              aclTemplateSet
                  .stream()
                  .filter(v -> v.get_nodeName().equals(anACL.get_nodeName()))
                  .collect(Collectors.toList())
                  .get(0);
          if (tokenDiff < tokenDifference(pickedOne._nameTokens, aclData._nameTokens)) {
            aclTemplateSet.remove(aclData);
            aclTemplateSet.add(anACL);
          }
        }
      }
    }

    private int tokenDifference(
        List<Pair<String, PreToken>> nameTokens, List<Pair<String, PreToken>> nameTokens1) {
      int differenceCount = 0;
      for (int i = 0; i < nameTokens.size(); i++) {
        if (!nameTokens.get(i).getFirst().equals(nameTokens1.get(i).getFirst())) {
          differenceCount += 1;
        }
      }
      return differenceCount;
    }

    private class ACLData {
      private String _nodeName;
      int _type;
      private List<Pair<String, PreToken>> _nameTokens;
      IpAccessList _acl;

      ACLData(String nodeName, int type, List<Pair<String, PreToken>> tokens, IpAccessList acl) {
        _nodeName = nodeName;
        _type = type;
        _nameTokens = tokens;
        _acl = acl;
      }

      String get_nodeName() {
        return _nodeName;
      }

      List<Pair<String, PreToken>> getNameTokens() {
        return _nameTokens;
      }

      IpAccessList get_acl() {
        return _acl;
      }
    }
  }

  // <question_page_comment>
  /**
   * Infers batfish JSON templates found in the nodes.
   *
   * <p>If many nodes follow a similar pattern to declare a data structure then we may generate a
   * template(anti-unifier) using least general generalization method.
   *
   * @type Templates multifile
   * @param nodeRegex Regular expression for names of nodes to include. Default value is '.*' (all
   *     nodes).
   */
  public static final class TemplatesQuestion extends Question {

    private static final String PROP_NODE_REGEX = "nodeRegex";

    private NodesSpecifier _nodeRegex;

    public TemplatesQuestion() {
      _nodeRegex = NodesSpecifier.ALL;
    }

    @Override
    public boolean getDataPlane() {
      return false;
    }

    @Override
    public String getName() {
      return "templates";
    }

    @JsonProperty(PROP_NODE_REGEX)
    public NodesSpecifier getNodeRegex() {
      return _nodeRegex;
    }

    @JsonProperty(PROP_NODE_REGEX)
    public void setNodeRegex(NodesSpecifier regex) {
      _nodeRegex = regex;
    }
  }

  @Override
  protected TemplateAnswerer createAnswerer(Question question, IBatfish batfish) {
    return new TemplateAnswerer(question, batfish);
  }

  @Override
  protected TemplatesQuestion createQuestion() {
    return new TemplatesQuestion();
  }
}
