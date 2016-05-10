package org.batfish.question.string_expr.route;

import org.batfish.datamodel.PrecomputedRoute;
import org.batfish.question.Environment;
import org.batfish.question.route_expr.RouteExpr;

public final class ProtocolRouteStringExpr extends RouteStringExpr {

   public ProtocolRouteStringExpr(RouteExpr caller) {
      super(caller);
   }

   @Override
   public String evaluate(Environment environment) {
      PrecomputedRoute caller = _caller.evaluate(environment);
      return caller.getProtocol().protocolName();
   }

}
