// Compiles against Hypergolic's real PublicAddressPolicy.java (no Android dependencies) and prints
// its verdict for resolved addresses and hostnames. Run (JDK 17+), from the napplets root:
//   javac -d OUT hypergolic/modules/napplet-host/android/src/main/java/org/nostrocket/hypergolic/host/PublicAddressPolicy.java lean/audits/hypergolic/validation/resource/AddressProbe.java
//   java -cp OUT org.nostrocket.hypergolic.host.AddressProbe
package org.nostrocket.hypergolic.host;
import java.net.InetAddress;
public final class AddressProbe {
  public static void main(String[] args) throws Exception {
    String[] ips = {"10.0.0.1","172.16.0.1","172.31.255.255","192.168.1.1","127.0.0.1","169.254.169.254","100.64.0.1","0.0.0.0",
      "255.255.255.255","224.0.0.1","192.0.0.8","198.18.0.1","::1","::","fc00::1","fd12::1","fe80::1","::ffff:10.0.0.1","::ffff:169.254.169.254",
      "64:ff9b::a00:1","2002:a00:1::","2001::1","ff02::1","93.184.216.34","2606:2800:220:1:248:1893:25c8:1946","172.32.0.1","100.128.0.1"};
    for (String ip : ips) System.out.println("ADDR " + ip + " accepted=" + PublicAddressPolicy.accepts(InetAddress.getByName(ip).getAddress()));
    String[] hosts = {"example.com","localhost","foo.local","10.0.0.1","0x7f.1","2130706433","0177.0.0.1","127.1","a.internal","[::1]","xn--80ak6aa92e.com","EXAMPLE.org","a_b.com","foo.home.arpa","1.2.3.4.nip.io"};
    for (String h : hosts) System.out.println("HOST " + h + " dnsHostname=" + PublicAddressPolicy.isDnsHostname(h));
  }
}
