package org.batfish.representation.cisco;

import java.io.Serializable;
import org.batfish.datamodel.Ip;

/** Representation of a NAT pool for Cisco devices. */
public final class NatPool implements Serializable {
  private static final long serialVersionUID = 1L;

  private final Ip _first;

  private final Ip _last;

  public NatPool(Ip first, Ip last) {
    _first = first;
    _last = last;
  }

  public Ip getFirst() {
    return _first;
  }

  public Ip getLast() {
    return _last;
  }
}
