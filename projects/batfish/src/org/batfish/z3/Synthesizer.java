package org.batfish.z3;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.batfish.common.BatfishException;
import org.batfish.common.util.SubRange;
import org.batfish.common.util.CommonUtil;
import org.batfish.datamodel.Edge;
import org.batfish.datamodel.IcmpCode;
import org.batfish.datamodel.IcmpType;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.IpProtocol;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.collections.EdgeSet;
import org.batfish.datamodel.collections.FibMap;
import org.batfish.datamodel.collections.FibRow;
import org.batfish.datamodel.collections.InterfaceSet;
import org.batfish.datamodel.collections.NodeInterfacePair;
import org.batfish.datamodel.collections.NodeSet;
import org.batfish.datamodel.collections.PolicyRouteFibIpMap;
import org.batfish.datamodel.collections.PolicyRouteFibNodeMap;
import org.batfish.datamodel.collections.RoleSet;
import org.batfish.representation.Configuration;
import org.batfish.representation.DataPlane;
import org.batfish.representation.Interface;
import org.batfish.representation.IpAccessList;
import org.batfish.representation.IpAccessListLine;
import org.batfish.representation.LineAction;
import org.batfish.representation.PolicyMap;
import org.batfish.representation.PolicyMapAction;
import org.batfish.representation.PolicyMapClause;
import org.batfish.representation.PolicyMapMatchIpAccessListLine;
import org.batfish.representation.PolicyMapMatchLine;
import org.batfish.representation.PolicyMapMatchType;
import org.batfish.representation.PolicyMapSetLine;
import org.batfish.representation.PolicyMapSetNextHopLine;
import org.batfish.representation.PolicyMapSetType;
import org.batfish.representation.TcpFlags;
import org.batfish.representation.Zone;
import org.batfish.z3.node.AcceptExpr;
import org.batfish.z3.node.AclDenyExpr;
import org.batfish.z3.node.AclMatchExpr;
import org.batfish.z3.node.AclNoMatchExpr;
import org.batfish.z3.node.AclPermitExpr;
import org.batfish.z3.node.AndExpr;
import org.batfish.z3.node.BooleanExpr;
import org.batfish.z3.node.Comment;
import org.batfish.z3.node.DebugExpr;
import org.batfish.z3.node.DeclareRelExpr;
import org.batfish.z3.node.DeclareVarExpr;
import org.batfish.z3.node.DestinationRouteExpr;
import org.batfish.z3.node.DropExpr;
import org.batfish.z3.node.EqExpr;
import org.batfish.z3.node.ExternalDestinationIpExpr;
import org.batfish.z3.node.ExternalSourceIpExpr;
import org.batfish.z3.node.ExtractExpr;
import org.batfish.z3.node.FalseExpr;
import org.batfish.z3.node.InboundInterfaceExpr;
import org.batfish.z3.node.IntExpr;
import org.batfish.z3.node.LitIntExpr;
import org.batfish.z3.node.NodeAcceptExpr;
import org.batfish.z3.node.NodeDropExpr;
import org.batfish.z3.node.NodeTransitExpr;
import org.batfish.z3.node.NonInboundNullSrcZoneExpr;
import org.batfish.z3.node.NonInboundSrcInterfaceExpr;
import org.batfish.z3.node.NonInboundSrcZoneExpr;
import org.batfish.z3.node.NotExpr;
import org.batfish.z3.node.OrExpr;
import org.batfish.z3.node.OriginateExpr;
import org.batfish.z3.node.PacketRelExpr;
import org.batfish.z3.node.PolicyDenyExpr;
import org.batfish.z3.node.PolicyExpr;
import org.batfish.z3.node.PolicyMatchExpr;
import org.batfish.z3.node.PolicyNoMatchExpr;
import org.batfish.z3.node.PolicyPermitExpr;
import org.batfish.z3.node.PostInExpr;
import org.batfish.z3.node.PostInInterfaceExpr;
import org.batfish.z3.node.PostOutInterfaceExpr;
import org.batfish.z3.node.PreInInterfaceExpr;
import org.batfish.z3.node.PreOutEdgeExpr;
import org.batfish.z3.node.PreOutExpr;
import org.batfish.z3.node.PreOutInterfaceExpr;
import org.batfish.z3.node.QueryRelationExpr;
import org.batfish.z3.node.RangeMatchExpr;
import org.batfish.z3.node.RoleAcceptExpr;
import org.batfish.z3.node.RoleOriginateExpr;
import org.batfish.z3.node.RuleExpr;
import org.batfish.z3.node.SaneExpr;
import org.batfish.z3.node.Statement;
import org.batfish.z3.node.TrueExpr;
import org.batfish.z3.node.UnoriginalExpr;
import org.batfish.z3.node.VarIntExpr;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Z3Exception;

public class Synthesizer {
   public static final int DSCP_BITS = 6;
   public static final String DSCP_VAR = "dscp";
   public static final String DST_IP_VAR = "dst_ip";
   public static final String DST_PORT_VAR = "dst_port";
   public static final int ECN_BITS = 2;
   public static final String ECN_VAR = "ecn";
   public static final String FLOW_SINK_TERMINATION_NAME = "flow_sink_termination";
   public static final int ICMP_CODE_BITS = 8;
   public static final String ICMP_CODE_VAR = "icmp_code";
   public static final int ICMP_TYPE_BITS = 8;
   public static final String ICMP_TYPE_VAR = "icmp_type";
   public static final int IP_BITS = 32;
   public static final String IP_PROTOCOL_VAR = "ip_prot";
   public static final String NODE_NONE_NAME = "(none)";
   public static final Map<String, Integer> PACKET_VAR_SIZES = initPacketVarSizes();
   public static final List<String> PACKET_VARS = getPacketVars();
   public static final int PORT_BITS = 16;
   public static final int PROTOCOL_BITS = 8;
   public static final String SRC_IP_VAR = "src_ip";
   public static final String SRC_PORT_VAR = "src_port";
   public static final int TCP_FLAGS_ACK_BITS = 1;
   public static final String TCP_FLAGS_ACK_VAR = "tcp_flags_ack";
   public static final int TCP_FLAGS_CWR_BITS = 1;
   public static final String TCP_FLAGS_CWR_VAR = "tcp_flags_cwr";
   public static final int TCP_FLAGS_ECE_BITS = 1;
   public static final String TCP_FLAGS_ECE_VAR = "tcp_flags_ece";
   public static final int TCP_FLAGS_FIN_BITS = 1;
   public static final String TCP_FLAGS_FIN_VAR = "tcp_flags_fin";
   public static final int TCP_FLAGS_PSH_BITS = 1;
   public static final String TCP_FLAGS_PSH_VAR = "tcp_flags_psh";
   public static final int TCP_FLAGS_RST_BITS = 1;
   public static final String TCP_FLAGS_RST_VAR = "tcp_flags_rst";
   public static final int TCP_FLAGS_SYN_BITS = 1;
   public static final String TCP_FLAGS_SYN_VAR = "tcp_flags_syn";
   public static final int TCP_FLAGS_URG_BITS = 1;
   public static final String TCP_FLAGS_URG_VAR = "tcp_flags_urg";

   @SuppressWarnings("unused")
   private static void debug(BooleanExpr condition, List<Statement> statements) {
      RuleExpr rule = new RuleExpr(condition, DebugExpr.INSTANCE);
      statements.add(rule);
   }

   private static List<String> getPacketVars() {
      List<String> vars = new ArrayList<String>();
      vars.add(SRC_IP_VAR);
      vars.add(DST_IP_VAR);
      vars.add(SRC_PORT_VAR);
      vars.add(DST_PORT_VAR);
      vars.add(IP_PROTOCOL_VAR);
      vars.add(DSCP_VAR);
      vars.add(ECN_VAR);
      vars.add(ICMP_TYPE_VAR);
      vars.add(ICMP_CODE_VAR);
      vars.add(TCP_FLAGS_CWR_VAR);
      vars.add(TCP_FLAGS_ECE_VAR);
      vars.add(TCP_FLAGS_URG_VAR);
      vars.add(TCP_FLAGS_ACK_VAR);
      vars.add(TCP_FLAGS_PSH_VAR);
      vars.add(TCP_FLAGS_RST_VAR);
      vars.add(TCP_FLAGS_SYN_VAR);
      vars.add(TCP_FLAGS_FIN_VAR);
      return vars;
   }

   public static Map<String, FuncDecl> getRelDeclFuncDecls(
         List<Statement> existingStatements, Context ctx) throws Z3Exception {
      Map<String, FuncDecl> funcDecls = new LinkedHashMap<String, FuncDecl>();
      Set<String> relations = new TreeSet<String>();
      for (Statement existingStatement : existingStatements) {
         relations.addAll(existingStatement.getRelations());
      }
      relations.add(QueryRelationExpr.NAME);
      for (String packetRel : relations) {
         List<Integer> sizes = new ArrayList<Integer>();
         sizes.addAll(PACKET_VAR_SIZES.values());
         DeclareRelExpr declaration = new DeclareRelExpr(packetRel, sizes);
         funcDecls.put(packetRel, declaration.toFuncDecl(ctx));
      }
      return funcDecls;
   }

   public static List<Statement> getVarDeclExprs() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment("Variable Declarations"));
      for (Entry<String, Integer> e : PACKET_VAR_SIZES.entrySet()) {
         String var = e.getKey();
         int size = e.getValue();
         statements.add(new DeclareVarExpr(var, size));
      }
      return statements;
   }

   public static String indent(int n) {
      String output = "";
      for (int i = 0; i < n; i++) {
         output += "   ";
      }
      return output;
   }

   private static Map<String, Integer> initPacketVarSizes() {
      Map<String, Integer> varSizes = new LinkedHashMap<String, Integer>();
      varSizes.put(SRC_IP_VAR, IP_BITS);
      varSizes.put(DST_IP_VAR, IP_BITS);
      varSizes.put(SRC_PORT_VAR, PORT_BITS);
      varSizes.put(DST_PORT_VAR, PORT_BITS);
      varSizes.put(IP_PROTOCOL_VAR, PROTOCOL_BITS);
      varSizes.put(DSCP_VAR, DSCP_BITS);
      varSizes.put(ECN_VAR, ECN_BITS);
      varSizes.put(ICMP_TYPE_VAR, ICMP_TYPE_BITS);
      varSizes.put(ICMP_CODE_VAR, ICMP_CODE_BITS);
      varSizes.put(TCP_FLAGS_CWR_VAR, TCP_FLAGS_CWR_BITS);
      varSizes.put(TCP_FLAGS_ECE_VAR, TCP_FLAGS_ECE_BITS);
      varSizes.put(TCP_FLAGS_URG_VAR, TCP_FLAGS_URG_BITS);
      varSizes.put(TCP_FLAGS_ACK_VAR, TCP_FLAGS_ACK_BITS);
      varSizes.put(TCP_FLAGS_PSH_VAR, TCP_FLAGS_PSH_BITS);
      varSizes.put(TCP_FLAGS_RST_VAR, TCP_FLAGS_RST_BITS);
      varSizes.put(TCP_FLAGS_SYN_VAR, TCP_FLAGS_SYN_BITS);
      varSizes.put(TCP_FLAGS_FIN_VAR, TCP_FLAGS_FIN_BITS);
      return varSizes;
   }

   private static boolean isLoopbackInterface(String ifaceName) {
      String lcIfaceName = ifaceName.toLowerCase();
      return lcIfaceName.startsWith("lo");
   }

   private static IntExpr newExtractExpr(String var, int low, int high) {
      int varSize = PACKET_VAR_SIZES.get(var);
      return newExtractExpr(var, varSize, low, high);
   }

   private static IntExpr newExtractExpr(String var, int varSize, int low,
         int high) {
      if (low == 0 && high == varSize - 1) {
         return new VarIntExpr(var);
      }
      else {
         return new ExtractExpr(var, low, high);
      }
   }

   private final Map<String, Configuration> _configurations;

   private final FibMap _fibs;

   private InterfaceSet _flowSinks;

   private final PolicyRouteFibNodeMap _prFibs;

   private final boolean _simplify;

   private final EdgeSet _topologyEdges;

   private final Map<String, Set<Interface>> _topologyInterfaces;

   private List<String> _warnings;

   public Synthesizer(Map<String, Configuration> configurations,
         boolean simplify) {
      _configurations = configurations;
      _fibs = null;
      _prFibs = null;
      _topologyEdges = null;
      _flowSinks = null;
      _simplify = simplify;
      _topologyInterfaces = null;
      _warnings = new ArrayList<String>();
   }

   public Synthesizer(Map<String, Configuration> configurations,
         DataPlane dataPlane, boolean simplify) {
      _configurations = configurations;
      _fibs = dataPlane.getFibs();
      _prFibs = dataPlane.getPolicyRouteFibNodeMap();
      _topologyEdges = dataPlane.getTopologyEdges();
      _flowSinks = dataPlane.getFlowSinks();
      _simplify = simplify;
      _topologyInterfaces = new TreeMap<String, Set<Interface>>();
      _warnings = new ArrayList<String>();
      computeTopologyInterfaces();
      pruneInterfaces();
   }

   private void computeTopologyInterfaces() {
      for (String hostname : _configurations.keySet()) {
         _topologyInterfaces.put(hostname, new TreeSet<Interface>());
      }
      for (Edge edge : _topologyEdges) {
         String hostname = edge.getNode1();
         if (!_topologyInterfaces.containsKey(hostname)) {
            _topologyInterfaces.put(hostname, new TreeSet<Interface>());
         }
         Set<Interface> interfaces = _topologyInterfaces.get(hostname);
         String interfaceName = edge.getInt1();
         Interface i = _configurations.get(hostname).getInterfaces()
               .get(interfaceName);
         interfaces.add(i);
      }
      for (String hostname : _configurations.keySet()) {
         Configuration c = _configurations.get(hostname);
         Map<String, Interface> nodeInterfaces = c.getInterfaces();
         for (String ifaceName : nodeInterfaces.keySet()) {
            if (isFlowSink(hostname, ifaceName)) {
               Interface iface = nodeInterfaces.get(ifaceName);
               if (iface.getActive()) {
                  Set<Interface> interfaces = _topologyInterfaces.get(hostname);
                  interfaces.add(iface);
               }
            }
         }
      }
   }

   private List<Statement> getAcceptRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment("Node accept lead to universal accept"));
      for (String nodeName : _configurations.keySet()) {
         NodeAcceptExpr nodeAccept = new NodeAcceptExpr(nodeName);
         RuleExpr connectAccepts = new RuleExpr(nodeAccept, AcceptExpr.INSTANCE);
         statements.add(connectAccepts);
      }
      return statements;
   }

   private List<Statement> getDestRouteToPreOutEdgeRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements
            .add(new Comment(
                  "Rules for sending destination routed packets to preoutIface stage"));
      for (String hostname : _fibs.keySet()) {
         TreeSet<FibRow> fibSet = _fibs.get(hostname);
         FibRow firstRow = fibSet.first();
         if (!firstRow.getPrefix().equals(Prefix.ZERO)) {
            // no default route, so add one that drops traffic
            FibRow dropDefaultRow = new FibRow(Prefix.ZERO,
                  FibRow.DROP_INTERFACE, "", "");
            fibSet.add(dropDefaultRow);
         }
         FibRow[] fib = fibSet.toArray(new FibRow[] {});
         for (int i = 0; i < fib.length; i++) {
            FibRow currentRow = fib[i];
            Set<FibRow> notRows = new TreeSet<FibRow>();
            for (int j = i + 1; j < fib.length; j++) {
               FibRow specificRow = fib[j];
               long currentStart = currentRow.getPrefix().getAddress().asLong();
               long currentEnd = currentRow.getPrefix().getEndAddress()
                     .asLong();
               long specificStart = specificRow.getPrefix().getAddress()
                     .asLong();
               long specificEnd = specificRow.getPrefix().getEndAddress()
                     .asLong();
               // check whether later prefix is contained in this one
               if (currentStart <= specificStart && specificEnd <= currentEnd) {
                  if (currentStart == specificStart
                        && currentEnd == specificEnd) {
                     // load balancing
                     continue;
                  }
                  if (currentRow.getInterface().equals(
                        specificRow.getInterface())
                        && currentRow.getNextHop().equals(
                              specificRow.getNextHop())
                        && currentRow.getNextHopInterface().equals(
                              specificRow.getNextHopInterface())) {
                     // no need to exclude packets matching the more specific
                     // prefix,
                     // since they would go out same edge
                     continue;
                  }
                  // exclude packets that match a more specific prefix that
                  // would go out a different interface
                  notRows.add(specificRow);
               }
               else {
                  break;
               }
            }
            AndExpr conditions = new AndExpr();
            DestinationRouteExpr destRoute = new DestinationRouteExpr(hostname);
            conditions.addConjunct(destRoute);
            String ifaceOutName = currentRow.getInterface();
            PacketRelExpr action;
            if (ifaceOutName.equals(FibRow.DROP_INTERFACE)
                  || isLoopbackInterface(ifaceOutName)
                  || CommonUtil.isNullInterface(ifaceOutName)) {
               action = new NodeDropExpr(hostname);
            }
            else {
               String nextHop = currentRow.getNextHop();
               String ifaceInName = currentRow.getNextHopInterface();
               action = new PreOutEdgeExpr(hostname, ifaceOutName, nextHop,
                     ifaceInName);
            }

            // must not match more specific routes
            for (FibRow notRow : notRows) {
               int prefixLength = notRow.getPrefix().getPrefixLength();
               long prefix = notRow.getPrefix().getAddress().asLong();
               int first = IP_BITS - prefixLength;
               if (first >= IP_BITS) {
                  continue;
               }
               int last = IP_BITS - 1;
               LitIntExpr prefixFragmentLit = new LitIntExpr(prefix, first,
                     last);
               IntExpr prefixFragmentExt = newExtractExpr(DST_IP_VAR, first,
                     last);
               NotExpr noPrefixMatch = new NotExpr();
               EqExpr prefixMatch = new EqExpr(prefixFragmentExt,
                     prefixFragmentLit);
               noPrefixMatch.SetArgument(prefixMatch);
               conditions.addConjunct(noPrefixMatch);
            }

            // must match route
            int prefixLength = currentRow.getPrefix().getPrefixLength();
            long prefix = currentRow.getPrefix().getAddress().asLong();
            int first = IP_BITS - prefixLength;
            if (first < IP_BITS) {
               int last = IP_BITS - 1;
               LitIntExpr prefixFragmentLit = new LitIntExpr(prefix, first,
                     last);
               IntExpr prefixFragmentExt = newExtractExpr(DST_IP_VAR, first,
                     last);
               EqExpr prefixMatch = new EqExpr(prefixFragmentExt,
                     prefixFragmentLit);
               conditions.addConjunct(prefixMatch);
            }

            // then we forward out specified interface (or drop)
            RuleExpr rule = new RuleExpr(conditions, action);
            statements.add(rule);
         }
      }
      return statements;
   }

   private List<Statement> getDropRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment("Node drop lead to universal drop"));
      for (String nodeName : _configurations.keySet()) {
         NodeDropExpr nodeDrop = new NodeDropExpr(nodeName);
         RuleExpr connectDrops = new RuleExpr(nodeDrop, DropExpr.INSTANCE);
         statements.add(connectDrops);
      }
      return statements;
   }

   private List<Statement> getExternalDstIpRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements
            .add(new Comment(
                  "Rule for matching external Source IP - one not assigned to an active interface of any provided node"));
      Set<Ip> interfaceIps = new TreeSet<Ip>();
      for (Entry<String, Configuration> e : _configurations.entrySet()) {
         Configuration c = e.getValue();
         for (Interface i : c.getInterfaces().values()) {
            if (i.getActive()) {
               Prefix prefix = i.getPrefix();
               if (prefix != null) {
                  Ip ip = prefix.getAddress();
                  interfaceIps.add(ip);
               }
            }
         }
      }
      OrExpr dstIpMatchesSomeInterfaceIp = new OrExpr();
      for (Ip ip : interfaceIps) {
         EqExpr dstIpMatchesSpecificInterfaceIp = new EqExpr(new VarIntExpr(
               DST_IP_VAR), new LitIntExpr(ip));
         dstIpMatchesSomeInterfaceIp
               .addDisjunct(dstIpMatchesSpecificInterfaceIp);
      }
      NotExpr externalDstIp = new NotExpr(dstIpMatchesSomeInterfaceIp);
      RuleExpr externalDstIpRule = new RuleExpr(externalDstIp,
            ExternalDestinationIpExpr.INSTANCE);
      statements.add(externalDstIpRule);
      return statements;
   }

   private List<Statement> getExternalSrcIpRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements
            .add(new Comment(
                  "Rule for matching external Source IP - one not assigned to an active interface of any provided node"));
      Set<Ip> interfaceIps = new TreeSet<Ip>();
      for (Entry<String, Configuration> e : _configurations.entrySet()) {
         Configuration c = e.getValue();
         for (Interface i : c.getInterfaces().values()) {
            if (i.getActive()) {
               Prefix prefix = i.getPrefix();
               if (prefix != null) {
                  Ip ip = prefix.getAddress();
                  interfaceIps.add(ip);
               }
            }
         }
      }
      OrExpr srcIpMatchesSomeInterfaceIp = new OrExpr();
      for (Ip ip : interfaceIps) {
         EqExpr srcIpMatchesSpecificInterfaceIp = new EqExpr(new VarIntExpr(
               SRC_IP_VAR), new LitIntExpr(ip));
         srcIpMatchesSomeInterfaceIp
               .addDisjunct(srcIpMatchesSpecificInterfaceIp);
      }
      NotExpr externalSrcIp = new NotExpr(srcIpMatchesSomeInterfaceIp);
      RuleExpr externalSrcIpRule = new RuleExpr(externalSrcIp,
            ExternalSourceIpExpr.INSTANCE);
      statements.add(externalSrcIpRule);
      return statements;
   }

   private List<Statement> getFlowSinkAcceptRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment(
            "Post out flow sink interface leads to node accept"));
      for (NodeInterfacePair f : _flowSinks) {
         String hostname = f.getHostname();
         String ifaceName = f.getInterface();
         if (isFlowSink(hostname, ifaceName)) {
            PostOutInterfaceExpr postOutIface = new PostOutInterfaceExpr(
                  hostname, ifaceName);
            NodeAcceptExpr nodeAccept = new NodeAcceptExpr(hostname);
            RuleExpr flowSinkAccept = new RuleExpr(postOutIface, nodeAccept);
            statements.add(flowSinkAccept);
         }
      }
      return statements;
   }

   private List<Statement> getInboundInterfaceToNodeAccept() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment(
            "Rules for connecting inbound_interface to node_accept"));
      for (Configuration c : _configurations.values()) {
         String hostname = c.getHostname();
         NodeAcceptExpr nodeAccept = new NodeAcceptExpr(hostname);
         for (Interface i : c.getInterfaces().values()) {
            String ifaceName = i.getName();
            InboundInterfaceExpr inboundInterface = new InboundInterfaceExpr(
                  hostname, ifaceName);
            // deal with origination totally independently of zone stuff
            AndExpr originateAcceptConditions = new AndExpr();
            OriginateExpr originate = new OriginateExpr(hostname);
            originateAcceptConditions.addConjunct(inboundInterface);
            originateAcceptConditions.addConjunct(originate);
            RuleExpr originateToNodeAccept = new RuleExpr(
                  originateAcceptConditions, nodeAccept);
            statements.add(originateToNodeAccept);

            Zone inboundZone = i.getZone();
            AndExpr acceptConditions = new AndExpr();
            acceptConditions.addConjunct(inboundInterface);
            if (inboundZone != null) {
               IpAccessList hostFilter = inboundZone.getToHostFilter();
               if (hostFilter != null) {
                  AclPermitExpr hostFilterPermit = new AclPermitExpr(hostname,
                        hostFilter.getName());
                  acceptConditions.addConjunct(hostFilterPermit);
               }
               String inboundFilterName;
               IpAccessList inboundInterfaceFilter = inboundZone
                     .getInboundInterfaceFilters().get(i);
               if (inboundInterfaceFilter != null) {
                  inboundFilterName = inboundInterfaceFilter.getName();
               }
               else {
                  IpAccessList inboundFilter = inboundZone.getInboundFilter();
                  inboundFilterName = inboundFilter.getName();
               }
               AclPermitExpr inboundFilterPermit = new AclPermitExpr(hostname,
                     inboundFilterName);
               acceptConditions.addConjunct(inboundFilterPermit);
            }
            else {
               // no inbound zone.
               // accept if packet was orginated at this node and default
               // inbound action is accept
               if (c.getDefaultInboundAction() == LineAction.REJECT
                     || c.getDefaultCrossZoneAction() == LineAction.REJECT) {
                  acceptConditions.addConjunct(originate);
               }
            }

            if (inboundZone != null) {
               OrExpr crossFilterSatisfied = new OrExpr();
               // If packet came in on inbound interface, accept.
               PostInInterfaceExpr postInInboundInterface = new PostInInterfaceExpr(
                     hostname, ifaceName);
               crossFilterSatisfied.addDisjunct(postInInboundInterface);

               // Otherwise, the packet must be permitted by the appropriate
               // cross-zone filter
               for (Zone srcZone : c.getZones().values()) {
                  AndExpr crossZoneConditions = new AndExpr();
                  String srcZoneName = srcZone.getName();
                  IpAccessList crossZoneFilter = srcZone.getToZonePolicies()
                        .get(inboundZone.getName());
                  NonInboundSrcZoneExpr nonInboundSrcZone = new NonInboundSrcZoneExpr(
                        hostname, srcZoneName);
                  crossZoneConditions.addConjunct(nonInboundSrcZone);

                  if (crossZoneFilter != null) {
                     AclPermitExpr crossZonePermit = new AclPermitExpr(
                           hostname, crossZoneFilter.getName());
                     crossZoneConditions.addConjunct(crossZonePermit);
                     crossFilterSatisfied.addDisjunct(crossZoneConditions);
                  }
                  else if (c.getDefaultCrossZoneAction() == LineAction.ACCEPT) {
                     crossFilterSatisfied.addDisjunct(crossZoneConditions);
                  }
               }
               // handle case where src interface is not in a zone
               if (c.getDefaultCrossZoneAction() == LineAction.ACCEPT) {
                  NonInboundNullSrcZoneExpr nonInboundNullSrcZone = new NonInboundNullSrcZoneExpr(
                        hostname);
                  crossFilterSatisfied.addDisjunct(nonInboundNullSrcZone);
               }
               acceptConditions.addConjunct(crossFilterSatisfied);
            }

            RuleExpr inboundInterfaceToNodeAccept = new RuleExpr(
                  acceptConditions, nodeAccept);
            statements.add(inboundInterfaceToNodeAccept);
         }
      }
      return statements;
   }

   private List<Statement> getInboundInterfaceToNodeDrop() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment(
            "Rules for connecting inbound_interface to node_deny"));
      for (Configuration c : _configurations.values()) {
         String hostname = c.getHostname();
         NodeDropExpr nodeDrop = new NodeDropExpr(hostname);
         UnoriginalExpr unoriginal = new UnoriginalExpr(hostname);
         for (Interface i : c.getInterfaces().values()) {
            String ifaceName = i.getName();
            InboundInterfaceExpr inboundInterface = new InboundInterfaceExpr(
                  hostname, ifaceName);
            Zone inboundZone = i.getZone();
            AndExpr dropConditions = new AndExpr();
            dropConditions.addConjunct(unoriginal);
            dropConditions.addConjunct(inboundInterface);
            OrExpr failConditions = new OrExpr();
            if (inboundZone != null) {
               IpAccessList hostFilter = inboundZone.getToHostFilter();
               if (hostFilter != null) {
                  AclDenyExpr hostFilterDeny = new AclDenyExpr(hostname,
                        hostFilter.getName());
                  failConditions.addDisjunct(hostFilterDeny);
               }
               String inboundFilterName;
               IpAccessList inboundInterfaceFilter = inboundZone
                     .getInboundInterfaceFilters().get(i);
               if (inboundInterfaceFilter != null) {
                  inboundFilterName = inboundInterfaceFilter.getName();
               }
               else {
                  IpAccessList inboundFilter = inboundZone.getInboundFilter();
                  inboundFilterName = inboundFilter.getName();
               }
               AclDenyExpr inboundFilterDeny = new AclDenyExpr(hostname,
                     inboundFilterName);
               failConditions.addDisjunct(inboundFilterDeny);
            }
            else if (c.getDefaultInboundAction() == LineAction.REJECT
                  || c.getDefaultCrossZoneAction() == LineAction.REJECT) {
               failConditions.addDisjunct(unoriginal);
            }

            if (inboundZone != null) {
               OrExpr crossFilterFailed = new OrExpr();
               // If packet didn't come in on inbound interface, drop if denied
               // by the appropriate cross-zone filter
               // permitted by the appropriate cross-zone policy
               for (Zone srcZone : c.getZones().values()) {
                  AndExpr crossZoneConditions = new AndExpr();
                  String srcZoneName = srcZone.getName();
                  IpAccessList crossZoneFilter = srcZone.getToZonePolicies()
                        .get(inboundZone.getName());
                  NonInboundSrcZoneExpr nonInboundSrcZone = new NonInboundSrcZoneExpr(
                        hostname, srcZoneName);
                  crossZoneConditions.addConjunct(nonInboundSrcZone);

                  if (crossZoneFilter != null) {
                     AclDenyExpr crossZoneDeny = new AclDenyExpr(hostname,
                           crossZoneFilter.getName());
                     crossZoneConditions.addConjunct(crossZoneDeny);
                     crossFilterFailed.addDisjunct(crossZoneConditions);
                  }
                  else if (c.getDefaultCrossZoneAction() == LineAction.REJECT) {
                     crossFilterFailed.addDisjunct(crossZoneConditions);
                  }
               }
               // handle case where src interface is not in a zone
               if (c.getDefaultCrossZoneAction() == LineAction.REJECT) {
                  NonInboundNullSrcZoneExpr nonInboundNullSrcZone = new NonInboundNullSrcZoneExpr(
                        hostname);
                  crossFilterFailed.addDisjunct(nonInboundNullSrcZone);
               }
               failConditions.addDisjunct(crossFilterFailed);
            }
            dropConditions.addConjunct(failConditions);
            RuleExpr inboundInterfaceToNodeDrop = new RuleExpr(dropConditions,
                  nodeDrop);
            statements.add(inboundInterfaceToNodeDrop);
         }
      }
      return statements;
   }

   private List<Statement> getMatchAclRules() {
      List<Statement> statements = new ArrayList<Statement>();
      Comment comment = new Comment("Rules for how packets can match acl lines");
      statements.add(comment);
      Map<String, Map<String, IpAccessList>> matchAcls = new TreeMap<String, Map<String, IpAccessList>>();
      // first we find out which acls we need to process
      // if data plane was provided as input, only check acls for topology
      // nodes/interfaces
      if (_topologyInterfaces != null) {
         for (String hostname : _topologyInterfaces.keySet()) {
            Configuration node = _configurations.get(hostname);
            Map<String, IpAccessList> aclMap = new TreeMap<String, IpAccessList>();
            Set<Interface> interfaces = _topologyInterfaces.get(hostname);
            for (Interface iface : interfaces) {
               if (iface.getPrefix() != null) {
                  IpAccessList aclIn = iface.getIncomingFilter();
                  IpAccessList aclOut = iface.getOutgoingFilter();
                  PolicyMap routePolicy = iface.getRoutingPolicy();
                  if (aclIn != null) {
                     String name = aclIn.getName();
                     aclMap.put(name, aclIn);
                  }
                  if (aclOut != null) {
                     String name = aclOut.getName();
                     aclMap.put(name, aclOut);
                  }
                  if (routePolicy != null) {
                     for (PolicyMapClause clause : routePolicy.getClauses()) {
                        for (PolicyMapMatchLine matchLine : clause
                              .getMatchLines()) {
                           if (matchLine.getType() == PolicyMapMatchType.IP_ACCESS_LIST) {
                              PolicyMapMatchIpAccessListLine matchAclLine = (PolicyMapMatchIpAccessListLine) matchLine;
                              for (IpAccessList acl : matchAclLine.getLists()) {
                                 String name = acl.getName();
                                 aclMap.put(name, acl);
                              }
                           }
                        }
                     }
                  }
               }
            }
            for (Zone zone : node.getZones().values()) {
               IpAccessList fromHostFilter = zone.getFromHostFilter();
               if (fromHostFilter != null) {
                  aclMap.put(fromHostFilter.getName(), fromHostFilter);
               }
               IpAccessList toHostFilter = zone.getToHostFilter();
               if (toHostFilter != null) {
                  aclMap.put(toHostFilter.getName(), toHostFilter);
               }
               IpAccessList inboundFilter = zone.getInboundFilter();
               if (inboundFilter != null) {
                  aclMap.put(inboundFilter.getName(), inboundFilter);
               }
               for (IpAccessList inboundInterfaceFilter : zone
                     .getInboundInterfaceFilters().values()) {
                  aclMap.put(inboundInterfaceFilter.getName(),
                        inboundInterfaceFilter);
               }
               for (IpAccessList toZoneFilter : zone.getToZonePolicies()
                     .values()) {
                  aclMap.put(toZoneFilter.getName(), toZoneFilter);
               }
            }
            if (aclMap.size() > 0) {
               matchAcls.put(hostname, aclMap);
            }
         }
      }
      else {
         // topology is null. just add all acls.
         for (Entry<String, Configuration> e : _configurations.entrySet()) {
            String hostname = e.getKey();
            Configuration c = e.getValue();
            matchAcls.put(hostname, c.getIpAccessLists());
         }
      }
      for (Entry<String, Map<String, IpAccessList>> e : matchAcls.entrySet()) {
         String hostname = e.getKey();
         Map<String, IpAccessList> aclMap = e.getValue();
         for (Entry<String, IpAccessList> e2 : aclMap.entrySet()) {
            String aclName = e2.getKey();
            IpAccessList acl = e2.getValue();
            List<IpAccessListLine> lines = acl.getLines();
            for (int i = 0; i < lines.size(); i++) {
               IpAccessListLine line = lines.get(i);
               // TODO: fix
               String invalidMessage = line.getInvalidMessage();
               boolean valid = invalidMessage == null;
               if (!valid) {
                  _warnings.add("WARNING: IpAccessList " + aclName + " line "
                        + i + ": disabled: " + invalidMessage + "\n");
               }

               Set<Prefix> srcIpRanges = line.getSourceIpRanges();
               Set<Prefix> srcOrDstIpRanges = line.getSrcOrDstIpRanges();
               Set<Prefix> dstIpRanges = line.getDestinationIpRanges();

               Set<IpProtocol> protocols = line.getProtocols();
               Set<SubRange> srcPortRanges = new LinkedHashSet<SubRange>();
               srcPortRanges.addAll(line.getSrcPortRanges());
               Set<SubRange> srcOrDstPortRanges = new LinkedHashSet<SubRange>();
               srcOrDstPortRanges.addAll(line.getSrcOrDstPortRanges());
               Set<SubRange> dstPortRanges = new LinkedHashSet<SubRange>();
               dstPortRanges.addAll(line.getDstPortRanges());
               int icmpType = line.getIcmpType();
               int icmpCode = line.getIcmpCode();
               List<TcpFlags> tcpFlags = line.getTcpFlags();
               Set<Integer> dscps = line.getDscps();
               Set<Integer> ecns = line.getEcns();

               AndExpr matchConditions = new AndExpr();

               // ** must not match previous rule **
               BooleanExpr prevNoMatch = (i > 0) ? new AclNoMatchExpr(hostname,
                     aclName, i - 1) : TrueExpr.INSTANCE;

               AndExpr matchLineCriteria = new AndExpr();
               matchConditions.addConjunct(matchLineCriteria);
               matchConditions.addConjunct(prevNoMatch);

               // match protocol
               if (protocols.size() > 0) {
                  OrExpr matchesSomeProtocol = new OrExpr();
                  for (IpProtocol protocol : protocols) {
                     int protocolNumber = protocol.number();
                     VarIntExpr protocolVar = new VarIntExpr(IP_PROTOCOL_VAR);
                     LitIntExpr protocolLit = new LitIntExpr(protocolNumber,
                           PROTOCOL_BITS);
                     EqExpr matchProtocol = new EqExpr(protocolVar, protocolLit);
                     matchesSomeProtocol.addDisjunct(matchProtocol);
                  }
                  matchLineCriteria.addConjunct(matchesSomeProtocol);
               }

               // match srcIp
               if (srcIpRanges.size() > 0) {
                  OrExpr matchSomeSrcIpRange = new OrExpr();
                  for (Prefix srcPrefix : srcIpRanges) {
                     long srcIp = srcPrefix.getAddress().asLong();

                     int srcIpWildcardBits = IP_BITS
                           - srcPrefix.getPrefixLength();
                     int srcIpStart = srcIpWildcardBits;
                     int srcIpEnd = IP_BITS - 1;
                     if (srcIpStart < IP_BITS) {
                        IntExpr extractsrcIp = newExtractExpr(SRC_IP_VAR,
                              srcIpStart, srcIpEnd);
                        LitIntExpr srcIpMatchLit = new LitIntExpr(srcIp,
                              srcIpStart, srcIpEnd);
                        EqExpr matchsrcIp = new EqExpr(extractsrcIp,
                              srcIpMatchLit);
                        matchSomeSrcIpRange.addDisjunct(matchsrcIp);
                     }
                     else {
                        matchSomeSrcIpRange.addDisjunct(TrueExpr.INSTANCE);
                     }
                  }
                  matchLineCriteria.addConjunct(matchSomeSrcIpRange);
               }

               // match srcOrDstIp
               if (srcOrDstIpRanges.size() > 0) {
                  OrExpr matchSomeSrcOrDstIpRange = new OrExpr();
                  for (Prefix srcOrDstPrefix : srcOrDstIpRanges) {
                     long srcOrDstIp = srcOrDstPrefix.getAddress().asLong();

                     int srcOrDstIpWildcardBits = IP_BITS
                           - srcOrDstPrefix.getPrefixLength();
                     int srcOrDstIpStart = srcOrDstIpWildcardBits;
                     int srcOrDstIpEnd = IP_BITS - 1;
                     if (srcOrDstIpStart < IP_BITS) {
                        IntExpr extractSrcIp = newExtractExpr(SRC_IP_VAR,
                              srcOrDstIpStart, srcOrDstIpEnd);
                        IntExpr extractDstIp = newExtractExpr(DST_IP_VAR,
                              srcOrDstIpStart, srcOrDstIpEnd);
                        LitIntExpr srcOrDstIpMatchLit = new LitIntExpr(
                              srcOrDstIp, srcOrDstIpStart, srcOrDstIpEnd);
                        EqExpr matchSrcIp = new EqExpr(extractSrcIp,
                              srcOrDstIpMatchLit);
                        EqExpr matchDstIp = new EqExpr(extractDstIp,
                              srcOrDstIpMatchLit);
                        matchSomeSrcOrDstIpRange.addDisjunct(matchSrcIp);
                        matchSomeSrcOrDstIpRange.addDisjunct(matchDstIp);
                     }
                     else {
                        matchSomeSrcOrDstIpRange.addDisjunct(TrueExpr.INSTANCE);
                     }
                  }
                  matchLineCriteria.addConjunct(matchSomeSrcOrDstIpRange);
               }

               // match dstIp
               if (dstIpRanges.size() > 0) {
                  OrExpr matchSomeDstIpRange = new OrExpr();
                  for (Prefix dstPrefix : dstIpRanges) {
                     long dstIp = dstPrefix.getAddress().asLong();

                     int dstIpWildcardBits = IP_BITS
                           - dstPrefix.getPrefixLength();
                     int dstIpStart = dstIpWildcardBits;
                     int dstIpEnd = IP_BITS - 1;
                     if (dstIpStart < IP_BITS) {
                        IntExpr extractDstIp = newExtractExpr(DST_IP_VAR,
                              dstIpStart, dstIpEnd);
                        LitIntExpr dstIpMatchLit = new LitIntExpr(dstIp,
                              dstIpStart, dstIpEnd);
                        EqExpr matchDstIp = new EqExpr(extractDstIp,
                              dstIpMatchLit);
                        matchSomeDstIpRange.addDisjunct(matchDstIp);
                     }
                     else {
                        matchSomeDstIpRange.addDisjunct(TrueExpr.INSTANCE);
                     }
                  }
                  matchLineCriteria.addConjunct(matchSomeDstIpRange);
               }

               // match srcPort
               if (srcPortRanges != null && srcPortRanges.size() > 0) {
                  BooleanExpr matchSrcPort = getMatchAclRules_portHelper(
                        srcPortRanges, SRC_PORT_VAR);
                  matchLineCriteria.addConjunct(matchSrcPort);
               }

               // match srcOrDstPort
               if (srcOrDstPortRanges != null && srcOrDstPortRanges.size() > 0) {
                  BooleanExpr matchSrcPort = getMatchAclRules_portHelper(
                        srcOrDstPortRanges, SRC_PORT_VAR);
                  BooleanExpr matchDstPort = getMatchAclRules_portHelper(
                        srcOrDstPortRanges, DST_PORT_VAR);
                  OrExpr matchSrcOrDstPort = new OrExpr();
                  matchSrcOrDstPort.addDisjunct(matchSrcPort);
                  matchSrcOrDstPort.addDisjunct(matchDstPort);
                  matchLineCriteria.addConjunct(matchSrcOrDstPort);
               }

               // match dstPort
               if (dstPortRanges != null && dstPortRanges.size() > 0) {
                  BooleanExpr matchDstPort = getMatchAclRules_portHelper(
                        dstPortRanges, DST_PORT_VAR);
                  matchLineCriteria.addConjunct(matchDstPort);
               }

               AclMatchExpr match = new AclMatchExpr(hostname, aclName, i);

               RuleExpr matchRule = new RuleExpr(valid ? matchConditions
                     : FalseExpr.INSTANCE, match);
               statements.add(matchRule);

               // match dscp
               if (!dscps.isEmpty()) {
                  OrExpr matchSomeDscp = new OrExpr();
                  matchLineCriteria.addConjunct(matchSomeDscp);
                  for (int dscp : dscps) {
                     EqExpr matchCurrentDscp = new EqExpr(new VarIntExpr(
                           DSCP_VAR), new LitIntExpr(dscp, DSCP_BITS));
                     matchSomeDscp.addDisjunct(matchCurrentDscp);
                  }
               }

               // match ecn
               if (!ecns.isEmpty()) {
                  OrExpr matchSomeEcn = new OrExpr();
                  matchLineCriteria.addConjunct(matchSomeEcn);
                  for (int ecn : ecns) {
                     EqExpr matchCurrentEcn = new EqExpr(
                           new VarIntExpr(ECN_VAR), new LitIntExpr(ecn,
                                 ECN_BITS));
                     matchSomeEcn.addDisjunct(matchCurrentEcn);
                  }
               }

               // match icmp-type
               if (icmpType != IcmpType.UNSET) {
                  EqExpr exactMatch = new EqExpr(new VarIntExpr(ICMP_TYPE_VAR),
                        new LitIntExpr(icmpType, ICMP_TYPE_BITS));
                  matchLineCriteria.addConjunct(exactMatch);
               }

               // match icmp-code
               if (icmpCode != IcmpCode.UNSET) {
                  EqExpr exactMatch = new EqExpr(new VarIntExpr(ICMP_CODE_VAR),
                        new LitIntExpr(icmpCode, ICMP_CODE_BITS));
                  matchLineCriteria.addConjunct(exactMatch);
               }

               // match tcp-flags
               if (!tcpFlags.isEmpty()) {
                  OrExpr matchSomeTcpFlags = new OrExpr();
                  matchLineCriteria.addConjunct(matchSomeTcpFlags);
                  for (TcpFlags currentTcpFlags : tcpFlags) {
                     AndExpr matchCurrentTcpFlags = new AndExpr();
                     matchSomeTcpFlags.addDisjunct(matchCurrentTcpFlags);
                     LitIntExpr one = new LitIntExpr(1, 1);
                     LitIntExpr zero = new LitIntExpr(0, 1);
                     if (currentTcpFlags.getUseCwr()) {
                        LitIntExpr bit = currentTcpFlags.getCwr() ? one : zero;
                        EqExpr matchFlag = new EqExpr(new VarIntExpr(
                              TCP_FLAGS_CWR_VAR), bit);
                        matchCurrentTcpFlags.addConjunct(matchFlag);
                     }
                     if (currentTcpFlags.getUseEce()) {
                        LitIntExpr bit = currentTcpFlags.getEce() ? one : zero;
                        EqExpr matchFlag = new EqExpr(new VarIntExpr(
                              TCP_FLAGS_ECE_VAR), bit);
                        matchCurrentTcpFlags.addConjunct(matchFlag);
                     }
                     if (currentTcpFlags.getUseUrg()) {
                        LitIntExpr bit = currentTcpFlags.getUrg() ? one : zero;
                        EqExpr matchFlag = new EqExpr(new VarIntExpr(
                              TCP_FLAGS_URG_VAR), bit);
                        matchCurrentTcpFlags.addConjunct(matchFlag);
                     }
                     if (currentTcpFlags.getUseAck()) {
                        LitIntExpr bit = currentTcpFlags.getAck() ? one : zero;
                        EqExpr matchFlag = new EqExpr(new VarIntExpr(
                              TCP_FLAGS_ACK_VAR), bit);
                        matchCurrentTcpFlags.addConjunct(matchFlag);
                     }
                     if (currentTcpFlags.getUsePsh()) {
                        LitIntExpr bit = currentTcpFlags.getPsh() ? one : zero;
                        EqExpr matchFlag = new EqExpr(new VarIntExpr(
                              TCP_FLAGS_PSH_VAR), bit);
                        matchCurrentTcpFlags.addConjunct(matchFlag);
                     }
                     if (currentTcpFlags.getUseRst()) {
                        LitIntExpr bit = currentTcpFlags.getRst() ? one : zero;
                        EqExpr matchFlag = new EqExpr(new VarIntExpr(
                              TCP_FLAGS_RST_VAR), bit);
                        matchCurrentTcpFlags.addConjunct(matchFlag);
                     }
                     if (currentTcpFlags.getUseSyn()) {
                        LitIntExpr bit = currentTcpFlags.getSyn() ? one : zero;
                        EqExpr matchFlag = new EqExpr(new VarIntExpr(
                              TCP_FLAGS_SYN_VAR), bit);
                        matchCurrentTcpFlags.addConjunct(matchFlag);
                     }
                     if (currentTcpFlags.getUseFin()) {
                        LitIntExpr bit = currentTcpFlags.getFin() ? one : zero;
                        EqExpr matchFlag = new EqExpr(new VarIntExpr(
                              TCP_FLAGS_FIN_VAR), bit);
                        matchCurrentTcpFlags.addConjunct(matchFlag);
                     }
                  }
               }
               // no match rule
               AndExpr noMatchConditions = new AndExpr();
               BooleanExpr noMatchLineCriteria = valid ? new NotExpr(
                     matchLineCriteria) : TrueExpr.INSTANCE;
               noMatchConditions.addConjunct(noMatchLineCriteria);
               noMatchConditions.addConjunct(prevNoMatch);
               AclNoMatchExpr noMatch = new AclNoMatchExpr(hostname, aclName, i);
               RuleExpr noMatchRule = new RuleExpr(noMatchConditions, noMatch);
               statements.add(noMatchRule);

               // permit/deny rule for match
               PolicyExpr aclAction;
               switch (line.getAction()) {
               case ACCEPT:
                  aclAction = new AclPermitExpr(hostname, aclName);
                  break;

               case REJECT:
                  aclAction = new AclDenyExpr(hostname, aclName);
                  break;

               default:
                  throw new Error("invalid action");
               }
               RuleExpr action = new RuleExpr(match, aclAction);
               statements.add(action);

            }
            // deny rule for not matching last line

            int lastLineIndex = acl.getLines().size() - 1;
            AclDenyExpr aclDeny = new AclDenyExpr(hostname, aclName);
            AclNoMatchExpr noMatchLast = new AclNoMatchExpr(hostname, aclName,
                  lastLineIndex);
            RuleExpr implicitDeny = new RuleExpr(noMatchLast, aclDeny);
            statements.add(implicitDeny);
         }
      }
      return statements;
   }

   private BooleanExpr getMatchAclRules_portHelper(Set<SubRange> ranges,
         String portVar) {
      return new RangeMatchExpr(portVar, PORT_BITS, ranges);
   }

   private List<Statement> getNodeAcceptToRoleAcceptRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment("Connect node_accept to role_accept"));
      for (Entry<String, Configuration> e : _configurations.entrySet()) {
         String hostname = e.getKey();
         Configuration c = e.getValue();
         NodeAcceptExpr nodeAccept = new NodeAcceptExpr(hostname);
         RoleSet roles = c.getRoles();
         if (roles != null) {
            for (String role : roles) {
               RoleAcceptExpr roleAccept = new RoleAcceptExpr(role);
               RuleExpr rule = new RuleExpr(nodeAccept, roleAccept);
               statements.add(rule);
            }
         }
      }
      return statements;
   }

   public NodeSet getNodeSet() {
      NodeSet nodes = new NodeSet();
      nodes.addAll(_configurations.keySet());
      return nodes;
   }

   private List<Statement> getOriginateToPostInRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment("Connect originate to post_in"));
      for (String hostname : _configurations.keySet()) {
         OriginateExpr originate = new OriginateExpr(hostname);
         PostInExpr postIn = new PostInExpr(hostname);
         RuleExpr rule = new RuleExpr(originate, postIn);
         statements.add(rule);
      }
      return statements;
   }

   private List<Statement> getPolicyRouteRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment("Policy-based routing rules"));

      for (Entry<String, Set<Interface>> e : _topologyInterfaces.entrySet()) {
         String hostname = e.getKey();
         PreOutExpr preOut = new PreOutExpr(hostname);
         PolicyRouteFibIpMap ipMap = _prFibs.get(hostname);
         Set<Interface> interfaces = e.getValue();
         for (Interface iface : interfaces) {
            String ifaceName = iface.getName();
            PostInInterfaceExpr postInInterface = new PostInInterfaceExpr(
                  hostname, ifaceName);
            PolicyMap p = iface.getRoutingPolicy();
            if (p != null) {
               String policyName = p.getMapName();
               PolicyPermitExpr permit = new PolicyPermitExpr(hostname,
                     policyName);
               PolicyDenyExpr deny = new PolicyDenyExpr(hostname, policyName);

               List<PolicyMapClause> clauses = p.getClauses();
               for (int i = 0; i < clauses.size(); i++) {
                  PolicyMapClause clause = clauses.get(i);
                  PolicyMapAction action = clause.getAction();
                  PolicyMatchExpr match = new PolicyMatchExpr(hostname,
                        policyName, i);
                  PolicyNoMatchExpr noMatch = new PolicyNoMatchExpr(hostname,
                        policyName, i);
                  BooleanExpr prevNoMatch = (i > 0) ? new PolicyNoMatchExpr(
                        hostname, policyName, i - 1) : TrueExpr.INSTANCE;
                  /**
                   * If clause matches, and clause number (matched) is that of a
                   * permit clause, and out interface is among next hops, then
                   * policy permit on out interface
                   */
                  switch (action) {
                  case PERMIT:
                     for (PolicyMapSetLine setLine : clause.getSetLines()) {
                        if (setLine.getType() == PolicyMapSetType.NEXT_HOP) {
                           PolicyMapSetNextHopLine setNextHopLine = (PolicyMapSetNextHopLine) setLine;
                           for (Ip nextHopIp : setNextHopLine.getNextHops()) {
                              EdgeSet edges = ipMap.get(nextHopIp);
                              /**
                               * If packet reaches postin_interface on inInt,
                               * and preout, and inInt has policy, and policy
                               * matches on out interface, then preout_edge on
                               * out interface and corresponding in interface
                               *
                               */
                              for (Edge edge : edges) {
                                 String outInterface = edge.getInt1();
                                 String nextHop = edge.getNode2();
                                 String inInterface = edge.getInt2();
                                 if (!hostname.equals(edge.getNode1())) {
                                    throw new BatfishException("Invalid edge");
                                 }
                                 AndExpr forwardConditions = new AndExpr();
                                 forwardConditions.addConjunct(postInInterface);
                                 forwardConditions.addConjunct(preOut);
                                 forwardConditions.addConjunct(match);
                                 if (CommonUtil.isNullInterface(outInterface)) {
                                    NodeDropExpr nodeDrop = new NodeDropExpr(
                                          hostname);
                                    RuleExpr dropRule = new RuleExpr(
                                          forwardConditions, nodeDrop);
                                    statements.add(dropRule);
                                 }
                                 else {
                                    PreOutEdgeExpr preOutEdge = new PreOutEdgeExpr(
                                          hostname, outInterface, nextHop,
                                          inInterface);
                                    RuleExpr preOutEdgeRule = new RuleExpr(
                                          forwardConditions, preOutEdge);
                                    statements.add(preOutEdgeRule);
                                 }
                              }
                           }
                        }
                     }
                     RuleExpr permitRule = new RuleExpr(match, permit);
                     statements.add(permitRule);
                     break;
                  case DENY:
                     /**
                      * If clause matches and clause is deny clause, just deny
                      */
                     RuleExpr denyRule = new RuleExpr(match, deny);
                     statements.add(denyRule);
                     break;
                  default:
                     throw new Error("bad action");
                  }

                  /**
                   * For each clause, if we reach that clause, then if any acl
                   * in that clause permits, or there are no acls, clause, if
                   * the packet then the packet is matched by that clause.
                   *
                   * If all (at least one) acls deny, then the packed is not
                   * matched by that clause
                   *
                   * If there are no acls to match, then the packet is matched
                   * by that clause.
                   *
                   */
                  boolean hasMatchIp = false;
                  AndExpr allAclsDeny = new AndExpr();
                  OrExpr someAclPermits = new OrExpr();
                  for (PolicyMapMatchLine matchLine : clause.getMatchLines()) {
                     if (matchLine.getType() == PolicyMapMatchType.IP_ACCESS_LIST) {
                        hasMatchIp = true;
                        PolicyMapMatchIpAccessListLine matchIpLine = (PolicyMapMatchIpAccessListLine) matchLine;
                        for (IpAccessList acl : matchIpLine.getLists()) {
                           String aclName = acl.getName();
                           AclDenyExpr currentAclDeny = new AclDenyExpr(
                                 hostname, aclName);
                           allAclsDeny.addConjunct(currentAclDeny);
                           AclPermitExpr currentAclPermit = new AclPermitExpr(
                                 hostname, aclName);
                           someAclPermits.addDisjunct(currentAclPermit);
                        }
                     }
                  }
                  AndExpr matchConditions = new AndExpr();
                  matchConditions.addConjunct(prevNoMatch);
                  if (hasMatchIp) {
                     /**
                      * no match if all acls deny
                      */
                     AndExpr noMatchConditions = new AndExpr();
                     noMatchConditions.addConjunct(prevNoMatch);
                     noMatchConditions.addConjunct(allAclsDeny);
                     RuleExpr noMatchRule = new RuleExpr(noMatchConditions,
                           noMatch);
                     statements.add(noMatchRule);

                     /**
                      * match if some acl permits
                      */
                     matchConditions.addConjunct(someAclPermits);
                  }
                  RuleExpr matchRule = new RuleExpr(matchConditions, match);
                  statements.add(matchRule);
               }
               /**
                * If the packet reaches the last clause, and is not matched by
                * that clause, then it is denied by the policy.
                */
               int lastIndex = p.getClauses().size() - 1;
               PolicyNoMatchExpr noMatchLast = new PolicyNoMatchExpr(hostname,
                     policyName, lastIndex);
               RuleExpr noMatchDeny = new RuleExpr(noMatchLast, deny);
               statements.add(noMatchDeny);
            }
         }
      }
      return statements;
   }

   private List<Statement> getPostInInterfaceToNonInboundSrcInterface() {
      List<Statement> statements = new ArrayList<Statement>();
      statements
            .add(new Comment(
                  "Rules for connecting postin_interface to non_inbound_src_interface"));
      for (Configuration c : _configurations.values()) {
         String hostname = c.getHostname();
         for (Interface i : c.getInterfaces().values()) {
            String ifaceName = i.getName();
            AndExpr conditions = new AndExpr();
            OrExpr dstIpMatchesInterface = new OrExpr();
            Prefix prefix = i.getPrefix();
            if (prefix != null) {
               Ip ip = prefix.getAddress();
               EqExpr dstIpMatches = new EqExpr(new VarIntExpr(DST_IP_VAR),
                     new LitIntExpr(ip));
               dstIpMatchesInterface.addDisjunct(dstIpMatches);
            }
            NotExpr dstIpNoMatchSrcInterface = new NotExpr(
                  dstIpMatchesInterface);
            conditions.addConjunct(dstIpNoMatchSrcInterface);
            PostInInterfaceExpr postInInterface = new PostInInterfaceExpr(
                  hostname, ifaceName);
            conditions.addConjunct(postInInterface);
            NonInboundSrcInterfaceExpr nonInboundSrcInterface = new NonInboundSrcInterfaceExpr(
                  hostname, ifaceName);
            Zone srcZone = i.getZone();
            if (srcZone != null) {
               NonInboundSrcZoneExpr nonInboundSrcZone = new NonInboundSrcZoneExpr(
                     hostname, srcZone.getName());
               RuleExpr nonInboundSrcInterfaceToNonInboundSrcZone = new RuleExpr(
                     nonInboundSrcInterface, nonInboundSrcZone);
               statements.add(nonInboundSrcInterfaceToNonInboundSrcZone);
            }
            else if (c.getDefaultCrossZoneAction() == LineAction.ACCEPT) {
               NonInboundNullSrcZoneExpr nonInboundNullSrcZone = new NonInboundNullSrcZoneExpr(
                     hostname);
               RuleExpr nonInboundSrcInterfaceToNonInboundNullSrcZone = new RuleExpr(
                     nonInboundSrcInterface, nonInboundNullSrcZone);
               statements.add(nonInboundSrcInterfaceToNonInboundNullSrcZone);
            }
            RuleExpr postInInterfaceToNonInboundSrcInterface = new RuleExpr(
                  conditions, nonInboundSrcInterface);
            statements.add(postInInterfaceToNonInboundSrcInterface);
         }
      }
      return statements;
   }

   private List<Statement> getPostInInterfaceToPostInRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment(
            "Rules for connecting postInInterface to postIn"));
      for (Entry<String, Set<Interface>> e : _topologyInterfaces.entrySet()) {
         String hostname = e.getKey();
         Set<Interface> interfaces = e.getValue();
         UnoriginalExpr unoriginal = new UnoriginalExpr(hostname);
         for (Interface i : interfaces) {
            String ifaceName = i.getName();
            PostInInterfaceExpr postInIface = new PostInInterfaceExpr(hostname,
                  ifaceName);
            PostInExpr postIn = new PostInExpr(hostname);
            RuleExpr postInInterfaceToPostIn = new RuleExpr(postInIface, postIn);
            statements.add(postInInterfaceToPostIn);
            RuleExpr postInInterfaceToUnoriginal = new RuleExpr(postInIface,
                  unoriginal);
            statements.add(postInInterfaceToUnoriginal);
         }
      }
      return statements;
   }

   private List<Statement> getPostInToInboundInterface() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment(
            "Rules for connecting post_in to inbound_interface"));
      for (Configuration c : _configurations.values()) {
         String hostname = c.getHostname();
         PostInExpr postIn = new PostInExpr(hostname);
         for (Interface i : c.getInterfaces().values()) {
            String ifaceName = i.getName();
            OrExpr dstIpMatchesInterface = new OrExpr();
            Prefix prefix = i.getPrefix();
            if (prefix != null) {
               Ip ip = prefix.getAddress();
               EqExpr dstIpMatches = new EqExpr(new VarIntExpr(DST_IP_VAR),
                     new LitIntExpr(ip));
               dstIpMatchesInterface.addDisjunct(dstIpMatches);
            }
            AndExpr inboundInterfaceConditions = new AndExpr();
            inboundInterfaceConditions.addConjunct(dstIpMatchesInterface);
            inboundInterfaceConditions.addConjunct(postIn);
            InboundInterfaceExpr inboundInterface = new InboundInterfaceExpr(
                  hostname, ifaceName);
            RuleExpr postInToInboundInterface = new RuleExpr(
                  inboundInterfaceConditions, inboundInterface);
            statements.add(postInToInboundInterface);
         }
      }
      return statements;
   }

   /*
    * private List<Statement> getPostInToNodeAcceptRules() { List<Statement>
    * statements = new ArrayList<Statement>(); statements .add(new
    * Comment("Rules for connecting post_in to node_accept")); for
    * (Configuration c : _configurations.values()) { String hostname =
    * c.getHostname(); PostInExpr postIn = new PostInExpr(hostname); for
    * (Interface i : c.getInterfaces().values()) { String ifaceName =
    * i.getName(); OrExpr someDstIpMatches = new OrExpr(); Prefix prefix =
    * i.getPrefix(); if (prefix != null) { Ip ip = prefix.getAddress(); EqExpr
    * dstIpMatches = new EqExpr(new VarIntExpr(DST_IP_VAR), new LitIntExpr(ip));
    * someDstIpMatches.addDisjunct(dstIpMatches); } AndExpr
    * inboundInterfaceConditions = new AndExpr();
    * inboundInterfaceConditions.addConjunct(someDstIpMatches);
    * inboundInterfaceConditions.addConjunct(postIn); InboundInterfaceExpr
    * inboundInterface = new InboundInterfaceExpr( hostname, ifaceName);
    * RuleExpr postInToInboundInterface = new RuleExpr(
    * inboundInterfaceConditions, inboundInterface); AndExpr acceptConditions =
    * new AndExpr(); PassHostFilterExpr passHostFilter = new
    * PassHostFilterExpr(hostname); PassInboundFilterExpr passInboundFilter =
    * new PassInboundFilterExpr( hostname, ifaceName); PostInInterfaceExpr
    * postInInterface = new PostInInterfaceExpr( hostname, ifaceName);
    * acceptConditions.addConjunct(postInInterface);
    * acceptConditions.addConjunct(passHostFilter);
    * acceptConditions.addConjunct(passInboundFilter);
    * statements.add(postInToInboundInterface); } NodeAcceptExpr nodeAccept =
    * new NodeAcceptExpr(hostname); AndExpr conditions = new AndExpr();
    * conditions.addConjunct(postIn); conditions.addConjunct(someDstIpMatches);
    * RuleExpr rule = new RuleExpr(conditions, nodeAccept);
    * statements.add(rule); } return statements; }
    */
   private List<Statement> getPostInToPreOutRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements
            .add(new Comment(
                  "postin ==> preout:",
                  "forward to preout if for each ip address on an interface, destination ip does not match"));
      for (Configuration c : _configurations.values()) {
         String hostname = c.getHostname();
         OrExpr someDstIpMatch = new OrExpr();
         for (Interface i : c.getInterfaces().values()) {
            Prefix prefix = i.getPrefix();
            if (prefix != null) {
               Ip ip = prefix.getAddress();
               EqExpr dstIpMatches = new EqExpr(new VarIntExpr(DST_IP_VAR),
                     new LitIntExpr(ip));
               someDstIpMatch.addDisjunct(dstIpMatches);
            }
         }
         NotExpr noDstIpMatch = new NotExpr(someDstIpMatch);
         PostInExpr postIn = new PostInExpr(hostname);
         PreOutExpr preOut = new PreOutExpr(hostname);
         AndExpr conditions = new AndExpr();
         conditions.addConjunct(postIn);
         conditions.addConjunct(noDstIpMatch);
         RuleExpr rule = new RuleExpr(conditions, preOut);
         statements.add(rule);
      }
      return statements;
   }

   private List<Statement> getPostOutIfaceToNodeTransitRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment(
            "Rules connecting postout_iface to node_transit"));
      for (Entry<String, Set<Interface>> e : _topologyInterfaces.entrySet()) {
         String hostname = e.getKey();
         Set<Interface> interfaces = e.getValue();
         NodeTransitExpr nodeTransit = new NodeTransitExpr(hostname);
         for (Interface iface : interfaces) {
            String ifaceName = iface.getName();
            PostOutInterfaceExpr postOutIface = new PostOutInterfaceExpr(
                  hostname, ifaceName);
            RuleExpr rule = new RuleExpr(postOutIface, nodeTransit);
            statements.add(rule);
         }
      }
      return statements;
   }

   private List<Statement> getPreInInterfaceToPostInInterfaceRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements
            .add(new Comment(
                  "Connect prein_interface to postin_interface, possibly through acl"));
      for (String hostname : _topologyInterfaces.keySet()) {
         Set<Interface> interfaces = _topologyInterfaces.get(hostname);
         for (Interface iface : interfaces) {
            String ifaceName = iface.getName();
            if (isFlowSink(hostname, ifaceName)) {
               continue;
            }
            NodeDropExpr nodeDrop = new NodeDropExpr(hostname);
            PreInInterfaceExpr preInIface = new PreInInterfaceExpr(hostname,
                  ifaceName);
            PostInInterfaceExpr postInIface = new PostInInterfaceExpr(hostname,
                  ifaceName);
            AndExpr conditions = new AndExpr();
            conditions.addConjunct(preInIface);
            IpAccessList inAcl = iface.getIncomingFilter();
            if (inAcl != null) {
               String aclName = inAcl.getName();
               AclPermitExpr aclPermit = new AclPermitExpr(hostname, aclName);
               conditions.addConjunct(aclPermit);
               AndExpr dropConditions = new AndExpr();
               AclDenyExpr aclDeny = new AclDenyExpr(hostname, aclName);
               dropConditions.addConjunct(preInIface);
               dropConditions.addConjunct(aclDeny);
               RuleExpr drop = new RuleExpr(dropConditions, nodeDrop);
               statements.add(drop);
            }
            RuleExpr preInToPostIn = new RuleExpr(conditions, postInIface);
            statements.add(preInToPostIn);
         }
      }
      return statements;
   }

   private List<Statement> getPreOutEdgeToPreOutInterfaceRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment("PreOutEdge => PreOutInterface"));
      for (NodeInterfacePair f : _flowSinks) {
         String hostnameOut = f.getHostname();
         String hostnameIn = NODE_NONE_NAME;
         String intOut = f.getInterface();
         String intIn = FLOW_SINK_TERMINATION_NAME;
         PreOutEdgeExpr preOutEdge = new PreOutEdgeExpr(hostnameOut, intOut,
               hostnameIn, intIn);
         PreOutInterfaceExpr preOutInt = new PreOutInterfaceExpr(hostnameOut,
               intOut);
         RuleExpr rule = new RuleExpr(preOutEdge, preOutInt);
         statements.add(rule);
      }
      for (Edge edge : _topologyEdges) {
         String hostnameOut = edge.getNode1();
         String hostnameIn = edge.getNode2();
         String intOut = edge.getInt1();
         String intIn = edge.getInt2();
         PreOutEdgeExpr preOutEdge = new PreOutEdgeExpr(hostnameOut, intOut,
               hostnameIn, intIn);
         PreOutInterfaceExpr preOutInt = new PreOutInterfaceExpr(hostnameOut,
               intOut);
         RuleExpr rule = new RuleExpr(preOutEdge, preOutInt);
         statements.add(rule);
      }
      return statements;
   }

   private List<Statement> getPreOutInterfaceToPostOutInterfaceRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements
            .add(new Comment(
                  "Connect preout_interface to postout_interface, possibly through acl"));
      for (String hostname : _topologyInterfaces.keySet()) {
         Configuration c = _configurations.get(hostname);
         Set<Interface> interfaces = _topologyInterfaces.get(hostname);
         OriginateExpr originate = new OriginateExpr(hostname);
         UnoriginalExpr unoriginal = new UnoriginalExpr(hostname);
         for (Interface iface : interfaces) {
            String ifaceName = iface.getName();
            NodeDropExpr nodeDrop = new NodeDropExpr(hostname);
            PreOutInterfaceExpr preOutIface = new PreOutInterfaceExpr(hostname,
                  ifaceName);
            PostOutInterfaceExpr postOutIface = new PostOutInterfaceExpr(
                  hostname, ifaceName);

            AndExpr outConditions = new AndExpr();
            AndExpr dropConditions = new AndExpr();
            outConditions.addConjunct(preOutIface);
            dropConditions.addConjunct(preOutIface);
            OrExpr filterDeny = new OrExpr();
            OrExpr crossZonePermit = new OrExpr();
            IpAccessList outAcl = iface.getOutgoingFilter();
            if (outAcl != null) {
               String aclName = outAcl.getName();
               AclPermitExpr aclPermit = new AclPermitExpr(hostname, aclName);
               outConditions.addConjunct(aclPermit);
               AclDenyExpr aclDeny = new AclDenyExpr(hostname, aclName);
               filterDeny.addDisjunct(aclDeny);
            }
            dropConditions.addConjunct(filterDeny);
            // handle cross-zone filter
            // first handle case where outgoing interface has no zone
            Zone outZone = iface.getZone();
            if (outZone == null) {
               if (c.getDefaultCrossZoneAction() == LineAction.REJECT) {
                  filterDeny.addDisjunct(unoriginal);
               }
               else {
                  crossZonePermit.addDisjunct(TrueExpr.INSTANCE);
               }
            }
            else {
               // outgoing interface has zone

               // now handle case of original packet
               IpAccessList fromHostFilter = outZone.getFromHostFilter();
               if (fromHostFilter != null) {
                  String fromHostFilterName = fromHostFilter.getName();
                  AclPermitExpr hostFilterPermit = new AclPermitExpr(hostname,
                        fromHostFilterName);
                  AndExpr originateCrossZonePermit = new AndExpr();
                  originateCrossZonePermit.addConjunct(hostFilterPermit);
                  originateCrossZonePermit.addConjunct(originate);
                  crossZonePermit.addDisjunct(originateCrossZonePermit);
                  AclDenyExpr hostFilterDeny = new AclDenyExpr(hostname,
                        fromHostFilterName);
                  AndExpr originateCrossZoneDeny = new AndExpr();
                  originateCrossZoneDeny.addConjunct(hostFilterDeny);
                  originateCrossZoneDeny.addConjunct(originate);
                  filterDeny.addDisjunct(originateCrossZoneDeny);
               }
               else {
                  crossZonePermit.addDisjunct(originate);
               }

               // now handle unoriginal packets
               // null src zone:
               NonInboundNullSrcZoneExpr nonInboundNullSrcZone = new NonInboundNullSrcZoneExpr(
                     hostname);
               if (c.getDefaultCrossZoneAction() == LineAction.REJECT) {
                  filterDeny.addDisjunct(nonInboundNullSrcZone);
               }
               else {
                  // default for null src zone is to accept
                  crossZonePermit.addDisjunct(nonInboundNullSrcZone);
               }

               // now handle cases of each possible src zone (still unoriginal)
               for (Zone srcZone : c.getZones().values()) {
                  String srcZoneName = srcZone.getName();
                  NonInboundSrcZoneExpr nonInboundSrcZone = new NonInboundSrcZoneExpr(
                        hostname, srcZoneName);
                  IpAccessList crossZoneFilter = srcZone.getToZonePolicies()
                        .get(outZone.getName());
                  // no policy for this pair of zones - use default cross-zone
                  // action
                  if (crossZoneFilter == null) {
                     if (c.getDefaultCrossZoneAction() == LineAction.REJECT) {
                        filterDeny.addDisjunct(nonInboundSrcZone);
                     }
                     else {
                        crossZonePermit.addDisjunct(nonInboundSrcZone);
                     }
                  }
                  else {
                     // there is a cross-zone filter
                     String crossZoneFilterName = crossZoneFilter.getName();
                     AclPermitExpr crossZoneFilterPermit = new AclPermitExpr(
                           hostname, crossZoneFilterName);
                     AclDenyExpr crossZoneFilterDeny = new AclDenyExpr(
                           hostname, crossZoneFilterName);
                     AndExpr deniedByCrossZoneFilter = new AndExpr();
                     deniedByCrossZoneFilter.addConjunct(nonInboundSrcZone);
                     deniedByCrossZoneFilter.addConjunct(crossZoneFilterDeny);
                     filterDeny.addDisjunct(deniedByCrossZoneFilter);
                     AndExpr allowedByCrossZoneFilter = new AndExpr();
                     allowedByCrossZoneFilter.addConjunct(nonInboundSrcZone);
                     allowedByCrossZoneFilter
                           .addConjunct(crossZoneFilterPermit);
                     crossZonePermit.addDisjunct(allowedByCrossZoneFilter);
                  }

               }
            }
            outConditions.addConjunct(crossZonePermit);
            RuleExpr drop = new RuleExpr(dropConditions, nodeDrop);
            statements.add(drop);
            RuleExpr preOutToPostOut = new RuleExpr(outConditions, postOutIface);
            statements.add(preOutToPostOut);
         }
      }
      return statements;
   }

   private List<Statement> getPreOutToDestRouteRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment(
            "Rules for sending packets from preout to destroute stage"));
      for (String hostname : _configurations.keySet()) {
         /**
          * if a packet whose source node is a given node reaches preout on that
          * node, then it reaches destroute
          */
         PreOutExpr preOut = new PreOutExpr(hostname);
         OriginateExpr originate = new OriginateExpr(hostname);
         DestinationRouteExpr destRoute = new DestinationRouteExpr(hostname);
         AndExpr originConditions = new AndExpr();
         originConditions.addConjunct(preOut);
         originConditions.addConjunct(originate);
         RuleExpr originDestRoute = new RuleExpr(originConditions, destRoute);
         statements.add(originDestRoute);
      }
      for (Entry<String, Set<Interface>> e : _topologyInterfaces.entrySet()) {
         String hostname = e.getKey();
         PreOutExpr preOut = new PreOutExpr(hostname);
         DestinationRouteExpr destRoute = new DestinationRouteExpr(hostname);
         Set<Interface> interfaces = e.getValue();
         for (Interface i : interfaces) {
            String ifaceName = i.getName();
            /**
             * if a packet reaches postin_interface on interface, and interface
             * is not policy-routed, and it reaches preout, then it reaches
             * destroute
             */
            /**
             * if a packet reaches postin_interface on intefrace, and interface
             * is policy-routed by policy, and policy denies, and it reaches
             * preout, then it reaches destroute
             *
             */
            PostInInterfaceExpr postInInterface = new PostInInterfaceExpr(
                  hostname, ifaceName);
            AndExpr receivedDestRouteConditions = new AndExpr();
            receivedDestRouteConditions.addConjunct(postInInterface);
            receivedDestRouteConditions.addConjunct(preOut);
            PolicyMap policy = i.getRoutingPolicy();
            if (policy != null) {
               String policyName = policy.getMapName();
               PolicyDenyExpr policyDeny = new PolicyDenyExpr(hostname,
                     policyName);
               receivedDestRouteConditions.addConjunct(policyDeny);
            }
            RuleExpr receivedDestRoute = new RuleExpr(
                  receivedDestRouteConditions, destRoute);
            statements.add(receivedDestRoute);
         }
      }
      return statements;
   }

   private List<Statement> getRoleOriginateToNodeOriginateRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment(
            "Rules connecting role_originate to R_originate"));
      for (Entry<String, Configuration> e : _configurations.entrySet()) {
         String hostname = e.getKey();
         Configuration c = e.getValue();
         OriginateExpr nodeOriginate = new OriginateExpr(hostname);
         RoleSet roles = c.getRoles();
         if (roles != null) {
            for (String role : roles) {
               RoleOriginateExpr roleOriginate = new RoleOriginateExpr(role);
               RuleExpr rule = new RuleExpr(roleOriginate, nodeOriginate);
               statements.add(rule);
            }
         }
      }
      return statements;
   }

   private List<Statement> getSane() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment("Make sure packet fields make sense"));
      AndExpr noPortNumbers = new AndExpr();
      EqExpr noDstPort = new EqExpr(new VarIntExpr(DST_PORT_VAR),
            new LitIntExpr(0, PORT_BITS));
      EqExpr noSrcPort = new EqExpr(new VarIntExpr(SRC_PORT_VAR),
            new LitIntExpr(0, PORT_BITS));
      noPortNumbers.addConjunct(noDstPort);
      noPortNumbers.addConjunct(noSrcPort);
      AndExpr noTcpFlags = new AndExpr();
      LitIntExpr zero = new LitIntExpr(0, 1);
      noTcpFlags
            .addConjunct(new EqExpr(new VarIntExpr(TCP_FLAGS_CWR_VAR), zero));
      noTcpFlags
            .addConjunct(new EqExpr(new VarIntExpr(TCP_FLAGS_ECE_VAR), zero));
      noTcpFlags
            .addConjunct(new EqExpr(new VarIntExpr(TCP_FLAGS_URG_VAR), zero));
      noTcpFlags
            .addConjunct(new EqExpr(new VarIntExpr(TCP_FLAGS_ACK_VAR), zero));
      noTcpFlags
            .addConjunct(new EqExpr(new VarIntExpr(TCP_FLAGS_PSH_VAR), zero));
      noTcpFlags
            .addConjunct(new EqExpr(new VarIntExpr(TCP_FLAGS_RST_VAR), zero));
      noTcpFlags
            .addConjunct(new EqExpr(new VarIntExpr(TCP_FLAGS_SYN_VAR), zero));
      noTcpFlags
            .addConjunct(new EqExpr(new VarIntExpr(TCP_FLAGS_FIN_VAR), zero));
      EqExpr noIcmpCode = new EqExpr(new VarIntExpr(ICMP_CODE_VAR),
            new LitIntExpr(IcmpCode.UNSET, ICMP_CODE_BITS));
      EqExpr noIcmpType = new EqExpr(new VarIntExpr(ICMP_TYPE_VAR),
            new LitIntExpr(IcmpType.UNSET, ICMP_TYPE_BITS));
      AndExpr noIcmp = new AndExpr();
      noIcmp.addConjunct(noIcmpType);
      noIcmp.addConjunct(noIcmpCode);
      EqExpr icmpProtocol = new EqExpr(new VarIntExpr(IP_PROTOCOL_VAR),
            new LitIntExpr(IpProtocol.ICMP.number(), PROTOCOL_BITS));
      EqExpr tcpProtocol = new EqExpr(new VarIntExpr(IP_PROTOCOL_VAR),
            new LitIntExpr(IpProtocol.TCP.number(), PROTOCOL_BITS));
      EqExpr udpProtocol = new EqExpr(new VarIntExpr(IP_PROTOCOL_VAR),
            new LitIntExpr(IpProtocol.UDP.number(), PROTOCOL_BITS));
      AndExpr tcp = new AndExpr();
      tcp.addConjunct(tcpProtocol);
      tcp.addConjunct(noIcmp);
      AndExpr udp = new AndExpr();
      udp.addConjunct(udpProtocol);
      udp.addConjunct(noIcmp);
      udp.addConjunct(noTcpFlags);
      AndExpr icmp = new AndExpr();
      icmp.addConjunct(icmpProtocol);
      icmp.addConjunct(noTcpFlags);
      icmp.addConjunct(noPortNumbers);
      AndExpr otherIp = new AndExpr();
      otherIp.addConjunct(noIcmp);
      otherIp.addConjunct(noTcpFlags);
      otherIp.addConjunct(noPortNumbers);
      OrExpr isSane = new OrExpr();
      isSane.addDisjunct(icmp);
      isSane.addDisjunct(tcp);
      isSane.addDisjunct(udp);
      isSane.addDisjunct(otherIp);
      RuleExpr rule = new RuleExpr(isSane, SaneExpr.INSTANCE);
      statements.add(rule);
      return statements;
   }

   private List<Statement> getToNeighborsRules() {
      List<Statement> statements = new ArrayList<Statement>();
      statements.add(new Comment("Topology edge rules"));
      for (Edge edge : _topologyEdges) {
         String hostnameOut = edge.getNode1();
         String hostnameIn = edge.getNode2();
         String intOut = edge.getInt1();
         String intIn = edge.getInt2();
         if (isFlowSink(hostnameIn, intIn) || isFlowSink(hostnameOut, intOut)) {
            continue;
         }

         PostOutInterfaceExpr postOutIface = new PostOutInterfaceExpr(
               hostnameOut, intOut);
         PreOutEdgeExpr preOutEdge = new PreOutEdgeExpr(hostnameOut, intOut,
               hostnameIn, intIn);
         PreInInterfaceExpr preInIface = new PreInInterfaceExpr(hostnameIn,
               intIn);
         AndExpr conditions = new AndExpr();
         conditions.addConjunct(postOutIface);
         conditions.addConjunct(preOutEdge);
         RuleExpr propagateToAdjacent = new RuleExpr(conditions, preInIface);
         statements.add(propagateToAdjacent);
      }
      return statements;
   }

   public List<String> getWarnings() {
      return _warnings;
   }

   private boolean isFlowSink(String hostname, String ifaceName) {
      NodeInterfacePair f = new NodeInterfacePair(hostname, ifaceName);
      return _flowSinks.contains(f);
   }

   private void pruneInterfaces() {
      for (Configuration c : _configurations.values()) {
         String hostname = c.getHostname();
         Set<String> prunedInterfaces = new HashSet<String>();
         Map<String, Interface> interfaces = c.getInterfaces();
         Set<Interface> topologyInterfaces = _topologyInterfaces.get(hostname);
         for (Interface i : interfaces.values()) {
            String ifaceName = i.getName();
            if ((!i.getActive() && !topologyInterfaces.contains(i))) {
               prunedInterfaces.add(ifaceName);
            }
            if (!i.getActive() && topologyInterfaces.contains(i)) {
               Interface blankInterface = new Interface(ifaceName, c);
               blankInterface.setActive(false);
               interfaces.put(ifaceName, blankInterface);
            }
         }
         for (String i : prunedInterfaces) {
            interfaces.remove(i);
         }
      }
   }

   public NodProgram synthesizeNodAclProgram(Context ctx) throws Z3Exception {

      List<Statement> ruleStatements = new ArrayList<Statement>();
      List<Statement> sane = getSane();
      List<Statement> matchAclRules = getMatchAclRules();

      ruleStatements.addAll(sane);
      ruleStatements.addAll(matchAclRules);
      return synthesizeNodProgram(ctx, ruleStatements);
   }

   public NodProgram synthesizeNodDataPlaneProgram(Context ctx)
         throws Z3Exception {
      List<Statement> ruleStatements = new ArrayList<Statement>();
      List<Statement> dropRules = getDropRules();
      List<Statement> acceptRules = getAcceptRules();
      List<Statement> sane = getSane();
      List<Statement> flowSinkAcceptRules = getFlowSinkAcceptRules();
      List<Statement> originateToPostInRules = getOriginateToPostInRules();
      List<Statement> postInInterfaceToPostInRules = getPostInInterfaceToPostInRules();
      List<Statement> postInInterfaceToNonInboundSrcInterface = getPostInInterfaceToNonInboundSrcInterface();
      List<Statement> postInToInboundInterface = getPostInToInboundInterface();
      List<Statement> inboundInterfaceToNodeAccept = getInboundInterfaceToNodeAccept();
      List<Statement> inboundInterfaceToNodeDrop = getInboundInterfaceToNodeDrop();
      List<Statement> postInToPreOutRules = getPostInToPreOutRules();
      List<Statement> preOutToDestRouteRules = getPreOutToDestRouteRules();
      List<Statement> destRouteToPreOutEdgeRules = getDestRouteToPreOutEdgeRules();
      List<Statement> preOutEdgeToPreOutInterfaceRules = getPreOutEdgeToPreOutInterfaceRules();
      List<Statement> policyRouteRules = getPolicyRouteRules();
      List<Statement> matchAclRules = getMatchAclRules();
      List<Statement> toNeighborsRules = getToNeighborsRules();
      List<Statement> preInInterfaceToPostInInterfaceRules = getPreInInterfaceToPostInInterfaceRules();
      List<Statement> preOutInterfaceToPostOutInterfaceRules = getPreOutInterfaceToPostOutInterfaceRules();
      List<Statement> nodeAcceptToRoleAcceptRules = getNodeAcceptToRoleAcceptRules();
      List<Statement> externalSrcIpRules = getExternalSrcIpRules();
      List<Statement> externalDstIpRules = getExternalDstIpRules();
      List<Statement> postOutIfaceToNodeTransitRules = getPostOutIfaceToNodeTransitRules();
      List<Statement> roleOriginateToNodeOriginateRules = getRoleOriginateToNodeOriginateRules();

      ruleStatements.addAll(dropRules);
      ruleStatements.addAll(acceptRules);
      ruleStatements.addAll(sane);
      ruleStatements.addAll(flowSinkAcceptRules);
      ruleStatements.addAll(originateToPostInRules);
      ruleStatements.addAll(postInInterfaceToPostInRules);
      ruleStatements.addAll(postInInterfaceToNonInboundSrcInterface);
      ruleStatements.addAll(postInToInboundInterface);
      ruleStatements.addAll(inboundInterfaceToNodeAccept);
      ruleStatements.addAll(inboundInterfaceToNodeDrop);
      ruleStatements.addAll(postInToPreOutRules);
      ruleStatements.addAll(preOutToDestRouteRules);
      ruleStatements.addAll(destRouteToPreOutEdgeRules);
      ruleStatements.addAll(preOutEdgeToPreOutInterfaceRules);
      ruleStatements.addAll(policyRouteRules);
      ruleStatements.addAll(matchAclRules);
      ruleStatements.addAll(toNeighborsRules);
      ruleStatements.addAll(preInInterfaceToPostInInterfaceRules);
      ruleStatements.addAll(preOutInterfaceToPostOutInterfaceRules);
      ruleStatements.addAll(nodeAcceptToRoleAcceptRules);
      ruleStatements.addAll(externalSrcIpRules);
      ruleStatements.addAll(externalDstIpRules);
      ruleStatements.addAll(postOutIfaceToNodeTransitRules);
      ruleStatements.addAll(roleOriginateToNodeOriginateRules);

      return synthesizeNodProgram(ctx, ruleStatements);
   }

   private NodProgram synthesizeNodProgram(Context ctx,
         List<Statement> ruleStatements) {
      NodProgram nodProgram = new NodProgram(ctx);
      Map<String, FuncDecl> relDeclFuncDecls = getRelDeclFuncDecls(
            ruleStatements, ctx);
      nodProgram.getRelationDeclarations().putAll(relDeclFuncDecls);
      Map<String, BitVecExpr> variables = nodProgram.getVariables();
      Map<String, BitVecExpr> variablesAsConsts = nodProgram
            .getVariablesAsConsts();
      int deBruinIndex = 0;
      for (Entry<String, Integer> e : PACKET_VAR_SIZES.entrySet()) {
         String var = e.getKey();
         int size = e.getValue();
         BitVecExpr varExpr = (BitVecExpr) ctx.mkBound(deBruinIndex,
               ctx.mkBitVecSort(size));
         BitVecExpr varAsConstExpr = (BitVecExpr) ctx.mkConst(var,
               ctx.mkBitVecSort(size));
         variables.put(var, varExpr);
         variablesAsConsts.put(var, varAsConstExpr);
         deBruinIndex++;
      }
      List<BoolExpr> rules = nodProgram.getRules();
      for (Statement rawStatement : ruleStatements) {
         Statement statement;
         if (_simplify) {
            statement = rawStatement.simplify();
         }
         else {
            statement = rawStatement;
         }
         if (statement instanceof RuleExpr) {
            RuleExpr ruleExpr = (RuleExpr) statement;
            BoolExpr rule = ruleExpr.toBoolExpr(nodProgram);
            rules.add(rule);
         }
      }
      return nodProgram;
   }

}
