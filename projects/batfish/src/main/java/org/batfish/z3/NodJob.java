package org.batfish.z3;

import com.google.common.collect.ImmutableSet.Builder;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import java.util.Map.Entry;
import java.util.SortedSet;
import javax.annotation.Nonnull;
import org.batfish.common.Pair;
import org.batfish.config.Settings;

public final class NodJob extends AbstractNodJob {

  private Synthesizer _dataPlaneSynthesizer;

  private QuerySynthesizer _querySynthesizer;

  public NodJob(
      Settings settings,
      Synthesizer dataPlaneSynthesizer,
      QuerySynthesizer querySynthesizer,
      SortedSet<Pair<String, String>> nodeVrfSet,
      String tag) {
    super(settings, nodeVrfSet, tag);
    _dataPlaneSynthesizer = dataPlaneSynthesizer;
    _querySynthesizer = querySynthesizer;
  }

  @Override
  protected BoolExpr computeSmtInput(
      long startTime, Context ctx, Builder<Entry<String, BitVecExpr>> variablesAsConstsBuilder) {
    NodProgram program = getNodProgram(ctx);
    variablesAsConstsBuilder.addAll(program.getNodContext().getVariablesAsConsts().entrySet());
    return computeSmtConstraintsViaNod(program, _querySynthesizer.getNegate());
  }

  @Nonnull protected NodProgram getNodProgram(Context ctx) {
    ReachabilityProgram baseProgram = _dataPlaneSynthesizer.synthesizeNodDataPlaneProgram();
    ReachabilityProgram queryProgram =
        _querySynthesizer.getReachabilityProgram(_dataPlaneSynthesizer.getInput());
    return new NodProgram(ctx, baseProgram, queryProgram);
  }
}
