package org.batfish.representation.cisco;

import java.io.Serializable;
import org.batfish.datamodel.RoutingProtocol;

public class BgpRedistributionPolicy extends RedistributionPolicy implements Serializable {

  public static final String OSPF_PROCESS_NUMBER = "OSPF_PROCESS_NUMBER";

  private static final long serialVersionUID = 1L;

  private Long _metric;

  public BgpRedistributionPolicy(RoutingProtocol sourceProtocol) {
    super(sourceProtocol, RoutingProtocol.BGP);
  }

  public Long getMetric() {
    return _metric;
  }

  public void setMetric(long metric) {
    _metric = metric;
  }
}
