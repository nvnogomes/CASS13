class Inc_thread implements Runnable {

	CCounter loc_cc;

	public Inc_thread(CCounter cc) {
	    loc_cc = cc;
	}

	public void run() { 
	    while(true){ loc_cc.inc(); ; System.out.println("inc");}
	}
    }


class Dec_thread implements Runnable {

	CCounter loc_cc;

	public Dec_thread(CCounter cc) {
	    loc_cc = cc;
	}

	public void run() { 
	    while(true) { loc_cc.dec(); System.out.println("dec"); }
	}
    }

public class Main {

    static Main dmain;

    public void doMain () {

        CCounter ccount = new CCounter();
	(new Thread(new Inc_thread(ccount))).start();
	(new Thread(new Dec_thread(ccount))).start();

    }

    public static void main(String[] args) 
    {
	new Main().doMain();
    }

}