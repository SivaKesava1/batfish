package org.batfish.z3;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Z3Exception;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.ForwardingAction;
import org.batfish.datamodel.HeaderSpace;
import org.batfish.z3.expr.AndExpr;
import org.batfish.z3.expr.BooleanExpr;
import org.batfish.z3.expr.HeaderSpaceMatchExpr;
import org.batfish.z3.expr.NotExpr;
import org.batfish.z3.expr.OrExpr;
import org.batfish.z3.expr.QueryExpr;
import org.batfish.z3.expr.RuleExpr;
import org.batfish.z3.expr.SaneExpr;
import org.batfish.z3.expr.visitors.BoolExprTransformer;
import org.batfish.z3.state.Accept;
import org.batfish.z3.state.Debug;
import org.batfish.z3.state.Drop;
import org.batfish.z3.state.DropAcl;
import org.batfish.z3.state.DropAclIn;
import org.batfish.z3.state.DropAclOut;
import org.batfish.z3.state.DropNoRoute;
import org.batfish.z3.state.DropNullRoute;
import org.batfish.z3.state.NodeAccept;
import org.batfish.z3.state.NodeDrop;
import org.batfish.z3.state.NodeDropAcl;
import org.batfish.z3.state.NodeDropAclIn;
import org.batfish.z3.state.NodeDropAclOut;
import org.batfish.z3.state.NodeDropNoRoute;
import org.batfish.z3.state.NodeDropNullRoute;
import org.batfish.z3.state.NodeTransit;
import org.batfish.z3.state.OriginateVrf;
import org.batfish.z3.state.Query;

public class ReachabilityQuerySynthesizer extends BaseQuerySynthesizer {

  private Set<ForwardingAction> _actions;

  private Set<String> _finalNodes;

  private HeaderSpace _headerSpace;

  private Map<String, Set<String>> _ingressNodeVrfs;

  private Set<String> _notTransitNodes;

  private Set<String> _transitNodes;

  public ReachabilityQuerySynthesizer(
      Set<ForwardingAction> actions,
      HeaderSpace headerSpace,
      Set<String> finalNodes,
      Map<String, Set<String>> ingressNodeVrfs,
      Set<String> transitNodes,
      Set<String> notTransitNodes) {
    _actions = actions;
    _finalNodes = finalNodes;
    _headerSpace = headerSpace;
    _ingressNodeVrfs = ingressNodeVrfs;
    _transitNodes = transitNodes;
    _notTransitNodes = notTransitNodes;
  }

  @Override
  public NodProgram getNodProgram(NodProgram baseProgram) throws Z3Exception {
    NodProgram program = new NodProgram(baseProgram.getContext());

    // create rules for injecting symbolic packets into ingress node(s)
    List<RuleExpr> originateRules = new ArrayList<>();
    for (String ingressNode : _ingressNodeVrfs.keySet()) {
      for (String ingressVrf : _ingressNodeVrfs.get(ingressNode)) {
        BooleanExpr originate = OriginateVrf.expr(ingressNode, ingressVrf);
        RuleExpr originateRule = new RuleExpr(originate);
        originateRules.add(originateRule);
      }
    }

    ImmutableList.Builder<BooleanExpr> queryConditionsBuilder = ImmutableList.builder();

    // create query condition for action at final node(s)
    ImmutableList.Builder<BooleanExpr> finalActionsBuilder = ImmutableList.builder();
    for (ForwardingAction action : _actions) {
      switch (action) {
        case ACCEPT:
          if (_finalNodes.size() > 0) {
            for (String finalNode : _finalNodes) {
              BooleanExpr accept = NodeAccept.expr(finalNode);
              finalActionsBuilder.add(accept);
            }
          } else {
            finalActionsBuilder.add(Accept.EXPR);
          }
          break;

        case DEBUG:
          finalActionsBuilder.add(Debug.EXPR);
          break;

        case DROP:
          if (_finalNodes.size() > 0) {
            for (String finalNode : _finalNodes) {
              BooleanExpr drop = NodeDrop.expr(finalNode);
              finalActionsBuilder.add(drop);
            }
          } else {
            finalActionsBuilder.add(Drop.EXPR);
          }
          break;

        case DROP_ACL:
          if (_finalNodes.size() > 0) {
            for (String finalNode : _finalNodes) {
              BooleanExpr drop = NodeDropAcl.expr(finalNode);
              finalActionsBuilder.add(drop);
            }
          } else {
            finalActionsBuilder.add(DropAcl.EXPR);
          }
          break;

        case DROP_ACL_IN:
          if (_finalNodes.size() > 0) {
            for (String finalNode : _finalNodes) {
              BooleanExpr drop = NodeDropAclIn.expr(finalNode);
              finalActionsBuilder.add(drop);
            }
          } else {
            finalActionsBuilder.add(DropAclIn.EXPR);
          }
          break;

        case DROP_ACL_OUT:
          if (_finalNodes.size() > 0) {
            for (String finalNode : _finalNodes) {
              BooleanExpr drop = NodeDropAclOut.expr(finalNode);
              finalActionsBuilder.add(drop);
            }
          } else {
            finalActionsBuilder.add(DropAclOut.EXPR);
          }
          break;

        case DROP_NO_ROUTE:
          if (_finalNodes.size() > 0) {
            for (String finalNode : _finalNodes) {
              BooleanExpr drop = NodeDropNoRoute.expr(finalNode);
              finalActionsBuilder.add(drop);
            }
          } else {
            finalActionsBuilder.add(DropNoRoute.EXPR);
          }
          break;

        case DROP_NULL_ROUTE:
          if (_finalNodes.size() > 0) {
            for (String finalNode : _finalNodes) {
              BooleanExpr drop = NodeDropNullRoute.expr(finalNode);
              finalActionsBuilder.add(drop);
            }
          } else {
            finalActionsBuilder.add(DropNullRoute.EXPR);
          }
          break;

        case FORWARD:
        default:
          throw new BatfishException("unsupported action");
      }
    }
    OrExpr finalActions = new OrExpr(finalActionsBuilder.build());
    queryConditionsBuilder.add(finalActions);
    queryConditionsBuilder.add(SaneExpr.INSTANCE);

    // check transit constraints (unordered)
    BooleanExpr transitExpr = null;
    for (String nodeName : _transitNodes) {
      transitExpr = NodeTransit.expr(nodeName);
      queryConditionsBuilder.add(transitExpr);
    }
    for (String nodeName : _notTransitNodes) {
      transitExpr = NodeTransit.expr(nodeName);
      queryConditionsBuilder.add(new NotExpr(transitExpr));
    }

    // add headerSpace constraints
    BooleanExpr matchHeaderSpace = new HeaderSpaceMatchExpr(_headerSpace);
    queryConditionsBuilder.add(matchHeaderSpace);
    AndExpr queryConditions = new AndExpr(queryConditionsBuilder.build());

    RuleExpr queryRule = new RuleExpr(queryConditions, Query.EXPR);
    List<BoolExpr> rules = program.getRules();
    for (RuleExpr originateRule : originateRules) {
      BoolExpr originateBoolExpr =
          BoolExprTransformer.toBoolExpr(originateRule.getSubExpression(), baseProgram);
      rules.add(originateBoolExpr);
    }
    rules.add(BoolExprTransformer.toBoolExpr(queryRule.getSubExpression(), baseProgram));
    QueryExpr query = new QueryExpr(Query.EXPR);
    BoolExpr queryBoolExpr = BoolExprTransformer.toBoolExpr(query.getSubExpression(), baseProgram);
    program.getQueries().add(queryBoolExpr);
    return program;
  }
}
