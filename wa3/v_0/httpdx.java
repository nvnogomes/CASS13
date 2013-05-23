// based on h.java, but with several changes 
//------------------------------------------  

import java.io.*;
import java.net.*;
import java.util.*;


class Listener implements Runnable {

Socket c;

Listener(Socket s)
{
    c = s;
}

public void run()
{
    try {
	    BufferedReader i=new BufferedReader(new InputStreamReader(c.getInputStream()));
	    DataOutputStream o=new DataOutputStream(c.getOutputStream());

	    try{
		String s,p;
		while((s=i.readLine()).length()>0)
		{
		    if(s.startsWith("GE")){
		    	String ss[] = s.split(" ");
		    	if (ss.length>1) {
		    		p = ss[1];
		    		if(p!=null){
		    			p=("."+(p.endsWith("/")?p+"index.html":p)).replace('/',File.separatorChar);
		    			int l;
                                        File f = new File(p);
                                        l=(int)f.length();
		    			byte[]b=new byte[l];
		    			new FileInputStream(p).read(b);
		    			o.writeBytes("HTTP/1.0 200 OK\nContent-type: text/html\n");
		    			o.writeBytes("Content-Length:"+Integer.toString(l+100)+"\n\n");
		    			o.write(b,0,l);
		    		}
		    	}
		    }
		}
		o.close();
	    }
	    catch(Exception e) { 
	    }

	} catch(Exception e){}
    }
}

public class httpdx
{ 

public static final int SOCKET = 8181;

public static void main(String[] args)
{
    try { 
	ServerSocket ss=new ServerSocket(SOCKET);
	for(;;)
	{
	    Listener l = new Listener(ss.accept());
	    (new Thread(l)).start();
	}
    }
    catch(Exception e){}
}

}

