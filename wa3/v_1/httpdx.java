// based on h.java, but with several changes
//------------------------------------------

import java.io.BufferedReader;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.net.ServerSocket;
import java.net.Socket;

/*@
 //duvida se e necessario isto ou a linha de baixo...
 //predicate Socket(InputStream i, OutputStream o) = i.InputStream() &*& o.OutputStream();
 predicate Socket(InputStream i, OutputStream o);

 //duvida: sera necessario o real p; ?
 //duvida se e necessario e ta bem feito o comando [p]Socket(?i, ?o);
 predicate threadInv(Listener l, real p;) =
 l.c |-> ?s &*&
 s != null &*& 
 [p]Socket(?i, ?o);
 @*/
class Listener implements Runnable {

	Socket c;
	boolean isActive;

	// @ predicate pre() = threadInv(this,1/4);
	// @ predicate post() = true;

	Listener()
	// @ requires s != null;
	// @ ensures threadInv(this,1/4);
	{
		isActive = true;
	}

	public void die() {
		isActive = false;
	}

	public void run()
	// @ requires pre();
	// @ ensures post();
	{
		while (isActive) {

			c = httpdx.socketQueue.dequeue();

			try {
				BufferedReader i = new BufferedReader(new InputStreamReader(
						c.getInputStream()));
				DataOutputStream o = new DataOutputStream(c.getOutputStream());

				try {
					String s, p;
					while ((s = i.readLine()).length() > 0) {
						if (s.startsWith("GE")) {
							String ss[] = s.split(" ");
							if (ss.length > 1) {
								p = ss[1];
								if (p != null) {
									p = ("." + (p.endsWith("/") ? p
											+ "index.html" : p)).replace('/',
											File.separatorChar);
									int l;
									File f = new File(p);
									l = (int) f.length();
									byte[] b = new byte[l];
									new FileInputStream(p).read(b);
									o.writeBytes("HTTP/1.0 200 OK\nContent-type: text/html\n");
									o.writeBytes("Content-Length:"
											+ Integer.toString(l + 100)
											+ "\n\n");
									o.write(b, 0, l);
								}
							}
						}
					}
					o.close();
				} catch (Exception e) {
				}

			} catch (Exception e) {
			}
		}
	}
}

public class httpdx {
	public static final int SOCKET = 8181;
	public static SocketQueue socketQueue;

	
	public static void main(String[] args)
	// @ requires true;
	// @ ensures true;
	{

		int numOfThreads = 2;
		if (args.length == 1) {
			numOfThreads = Integer.parseInt(args[0]);

			if (numOfThreads < 0 || numOfThreads > 40) {
				System.err.println("Error: unacceptable number of threads");
			}
		} else {
			System.out.println("INFO: using default number of threads (2)");
		}

		socketQueue = new SocketQueue( numOfThreads );

		// init threads
		Listener threadPool[] = new Listener[numOfThreads];
		for (int i = 0; i < numOfThreads; i++) {
			threadPool[i] = new Listener();
			(new Thread(threadPool[i])).start();
		}

		try {
			ServerSocket ss = new ServerSocket(SOCKET);
			for (;;) {
				socketQueue.enqueue(ss.accept());
			}
		} catch (Exception e) {
		} 
//		finally { // verifast parser doesnt recognize finally
			// kill threads (unreachable code??)
			for (int i = 0; i < numOfThreads; i++) {
				threadPool[i].die();
			}
//		}
	}

}
