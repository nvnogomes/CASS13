package CHashMapMain;

	/*@
	predicate Rem_threadInv(Rem_thread t, real p;) = t.loc_cc |-> ?cc &*& cc != null &*& [p]CHashMapInv(cc);
	predicate Get_threadInv(Get_thread t, real p;) = t.loc_cc |-> ?cc &*& cc != null &*& [p]CHashMapInv(cc);
	@*/
	
class Get_thread implements Runnable {

	public CHashMap loc_cc;

	//@ predicate pre() = Get_threadInv(this,1/4);
        //@ predicate post() = true;

	public Get_thread(CHashMap cc)
	//@ requires cc != null &*& [1/4]CHashMapInv(cc); 
	//@ ensures Get_threadInv(this,1/4);
	{
	    loc_cc = cc;
	}

	public void run() 
        //@ requires pre();
        //@ ensures post();
	{ 
	    while(true)
	    //@ invariant Get_threadInv(this,1/4);
		{ loc_cc.remove(null);}
	}
    }

class Rem_thread implements Runnable {

	CHashMap loc_cc;
	
	//@ predicate pre() = Rem_threadInv(this,1/2);
        //@ predicate post() = true;
        
	public Rem_thread(CHashMap cc)
	//@ requires cc != null &*& [1/2]CHashMapInv(cc);
	//@ ensures Rem_threadInv(this,1/2);
	{
	    loc_cc = cc;
	}

	public void run()
	//@ requires pre();
    	//@ ensures post();	
	{ 
	    while(true)
	 //@ invariant Rem_threadInv(this,1/2);
	   { loc_cc.get(null); }
	}
    }

public class Main {

    public void doMain ()
    //@ requires true;
    //@ ensures true;
    {
        CHashMap ccount = new CHashMap();
        Get_thread it1 = new Get_thread(ccount);  
	(new Thread(it1)).start();
	Get_thread it2 = new Get_thread(ccount);  
	(new Thread(it2)).start();
	Rem_thread dt = new Rem_thread(ccount); 
	Thread dtt = new Thread(dt);
	dtt.start();
    }

    public static void main(String[] args) 
    //@ requires true;
    //@ ensures true;
    {
	new Main().doMain();
    }

}
