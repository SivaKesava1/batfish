package org.batfish.representation.palo_alto;

import java.io.Serializable;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Prefix;

public class StaticRoute implements Serializable {

  private static final long serialVersionUID = 1L;

  /* https://www.paloaltonetworks.com/documentation/80/pan-os/pan-os/networking/static-routes/static-route-overview */
  private static final int DEFAULT_ADMIN_DISTANCE = 10;

  /* Static routes show up with default metric of 10 when showing routes on PAN device */
  private static final int DEFAULT_METRIC = 10;

  private int _adminDistance;

  private Prefix _destination;

  private int _metric;

  private final String _name;

  private String _nextHopInterface;

  private Ip _nextHopIp;

  public StaticRoute(String name) {
    _name = name;
    _adminDistance = DEFAULT_ADMIN_DISTANCE;
    _metric = DEFAULT_METRIC;
  }

  public int getAdminDistance() {
    return _adminDistance;
  }

  public Prefix getDestination() {
    return _destination;
  }

  public int getMetric() {
    return _metric;
  }

  public String getName() {
    return _name;
  }

  public String getNextHopInterface() {
    return _nextHopInterface;
  }

  public Ip getNextHopIp() {
    return _nextHopIp;
  }

  public void setAdminDistance(int adminDistance) {
    _adminDistance = adminDistance;
  }

  public void setDestination(Prefix destination) {
    _destination = destination;
  }

  public void setMetric(int metric) {
    _metric = metric;
  }

  public void setNextHopInterface(String nextHopInterface) {
    _nextHopInterface = nextHopInterface;
  }

  public void setNextHopIp(Ip nextHopIp) {
    _nextHopIp = nextHopIp;
  }
}
