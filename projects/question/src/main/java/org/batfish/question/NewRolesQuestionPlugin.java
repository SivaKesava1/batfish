package org.batfish.question;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.auto.service.AutoService;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.Pair;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.questions.NodesSpecifier;
import org.batfish.datamodel.questions.Question;
import org.batfish.role.InferRoles;
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

      SortedMap<Long, SortedSet<String>> possibleBorderRouters = inferBorderNodes(borderNodes);

      if(borderNodes.size()>0){

      }

      NodeRoleDimension roleDimension =
          _batfish
              .getNodeRoleDimension(question.getRoleDimension())
              .orElseThrow(
                  () ->
                      new BatfishException(
                          "No role dimension found for " + question.getRoleDimension()));

      NewRolesAnswerElement answerElement =
          new NewRolesAnswerElement(roleDimension, roleDimension.createRoleNodesMap(nodes));

      return answerElement;
    }

    private SortedMap<Long, SortedSet<String>> inferBorderNodes(Set<String> borderNodes) {
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
                  & neighbor.getLocalAs() < 64512) {
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
      if(copyBorderNodes.size() >0){
        possibleBorderRouters.put(0L, new TreeSet<>(copyBorderNodes));
      }
      return possibleBorderRouters;
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
   */
  public static final class NewRolesQuestion extends Question {

    private static final String PROP_NODE_REGEX = "nodeRegex";

    private static final String PROP_ROLE_DIMENSION = "roleDimension";

    private static final String PROP_BORDER_NODE_REGEX = "borderNodeRegex";

    @Nonnull private NodesSpecifier _nodeRegex;
    @Nonnull private NodesSpecifier _borderNodeRegex;

    @Nullable private String _roleDimension;

    @JsonCreator
    public NewRolesQuestion(
        @JsonProperty(PROP_NODE_REGEX) NodesSpecifier nodeRegex,
        @JsonProperty(PROP_BORDER_NODE_REGEX) NodesSpecifier borderNodeRegex,
        @JsonProperty(PROP_ROLE_DIMENSION) String roleDimension) {
      _nodeRegex = nodeRegex == null ? NodesSpecifier.ALL : nodeRegex;
      _roleDimension = roleDimension;
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
  }

  @Override
  protected Answerer createAnswerer(Question question, IBatfish batfish) {
    return new NewRolesAnswerer(question, batfish);
  }

  @Override
  protected Question createQuestion() {
    return new NewRolesQuestion(null, null, null);
  }
}
