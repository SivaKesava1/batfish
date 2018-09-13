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
import java.util.stream.Collectors;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.Pair;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Interface;
import org.batfish.datamodel.IpAccessList;
import org.batfish.datamodel.IpAccessListLine;
import org.batfish.datamodel.LineAction;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.collections.NamedStructureEquivalenceSets;
import org.batfish.datamodel.questions.NodesSpecifier;
import org.batfish.datamodel.questions.Question;
import org.batfish.role.InferRoles.PreToken;

@AutoService(Plugin.class)
public class TemplatesQuestionPlugin extends QuestionPlugin {

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
     basedOnNames();
      return answerElement;
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
      System.out.println("hello");
    }

    private class ACLData{
      String _nodeName;
      int _type;
      List<Pair<String, PreToken>> _nameTokens;
      IpAccessList _acl;

      ACLData(String nodeName, int type, List<Pair<String, PreToken>> tokens, IpAccessList acl){
        _nodeName = nodeName;
        _type = type;
        _nameTokens = tokens;
        _acl = acl;
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
