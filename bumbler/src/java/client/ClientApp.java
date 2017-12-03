/** @file
  * @author Igor Lesik 2016
  *
  *
  */
package client;

import bmb.util.ConsoleProgressBar;

public class ClientApp {

    public static void main(String[] args) {

        System.out.println("Client App");

        java.net.Socket connection = tryToConnect("localhost", 1883, 20);

        if (!connection.isConnected()) {
            System.out.println("Can't connect to server.");
            return;
        }

        System.out.println("Connected to server");

try{
        //java.net.Socket connection = new java.net.Socket("localhost", 1883/*Port*/);
        //java.io.DataOutputStream output = new java.io.DataOutputStream(connection.getOutputStream());
        bmb.net.TcpDataOutputStream output = new bmb.net.TcpDataOutputStream(connection.getOutputStream());

        java.util.Scanner sc = new java.util.Scanner(System.in);

        while(true) {
            //output.writeBytes(sc.nextLine());
            String s = sc.nextLine();
            byte[] b = s.getBytes(java.nio.charset.Charset.forName("UTF-8")/*StandardCharsets.UTF_8*/);
            output.writePacket(b, 0, b.length);
        }

}
catch(java.io.IOException e) {
    System.err.println("Caught IOException: " + e.getMessage());
}

    }

/** Returns connected or un-connected Socket.
 * 
 */
static java.net.Socket
tryToConnect(String host, int port, int timeout)
{
    // create un-connected socket
    java.net.Socket socket = new java.net.Socket();

    ConsoleProgressBar progress = new ConsoleProgressBar();

    int timer = timeout;

    System.out.printf("Connecting to server %s:%d\n", host, port);

    do {
        try {
            java.net.Socket connected_socket = new java.net.Socket(host, port);
            socket = connected_socket;
            if (timer != timeout) {
                progress.update(timeout, timeout);
            }
            break;
        }
        catch (java.io.IOException e) {
            progress.update(timeout - timer, timeout);
        }

        try {
            java.util.concurrent.TimeUnit.SECONDS.sleep(1);
        } catch(InterruptedException e) {
            //Thread.currentThread().interrupt();
        }
    } while (--timer > 0);

    return socket;
}


}
