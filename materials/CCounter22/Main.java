package CCounterMain;

	/*@
	predicate Inc_thread_counter_frac(real p;) = emp;
	predicate Inc_threadInv(Inc_thread t;) =
		t.loc_cc |-> ?cc &*& 
		cc != null &*& 
		t.ff |-> ?f &*&
		[f]CCounterInv(cc);
	
	predicate Dec_thread_counter_frac(real p;) = emp;
	predicate Dec_threadInv(Dec_thread t;) =
		t.loc_cc |-> ?cc &*&
		cc != null &*&
		t.ff |-> ?f &*& 
		[f]CCounterInv(cc);
	@*/
	
class Inc_thread implements Runnable {

	public CCounter loc_cc;

	// ghost variable ff holds the fraction of CCounterInv used by this thread
	// see Inc_threadInv above, by accessing this.ff
	
	//@ real ff;

	//@ predicate pre()  = Inc_threadInv(this);
        //@ predicate post() = true;

	public Inc_thread(CCounter cc)
	//@ requires cc != null &*& [?f]CCounterInv(cc); 
	//@ ensures Inc_threadInv(this);
	{
	    loc_cc = cc;
	    //@ ff = f;
	}

	public void run() 
        //@ requires pre();
        //@ ensures post();
	{ 
	    //@ assert Inc_threadInv(this);
	    while(true)
	    //@ invariant Inc_threadInv(this);
		{
		  loc_cc.inc();
		}
	}
    }

class Dec_thread implements Runnable {

	CCounter loc_cc;
        //@ real ff;
        
	//@ predicate pre() = Dec_threadInv(this);
        //@ predicate post() = true;
        
	public Dec_thread(CCounter cc)
	//@ requires cc != null &*& [?f]CCounterInv(cc);
	//@ ensures Dec_threadInv(this);
	{
	    loc_cc = cc;
	    //@ ff = f;
	}

	public void run()
	//@ requires pre();
    	//@ ensures post();	
	{ 
	    while(true)
	    //@ invariant Dec_threadInv(this);
	    { loc_cc.dec(); }
	}
    }
 
/*@

predicate_ctor CCounter_fracs (CCounter c) () = CCounterInv(c) ;

@*/

public class Main {

    // The next two methods use the fraction manager.
    // See definitions in java.lang.javaspec.
    // create_fractionable_chunk(predicate () p) reserves a fraction of the assertion given by predicate constructor p
    // steal_fraction(predicate () p) exposes half of the currently reserved fraction 
    
        public void doMain2 ()
    //@ requires emp;
    //@ ensures emp;
    {
        CCounter ccount = new CCounter();
        //@ close CCounter_fracs (ccount)();
        //@ create_fractionable_chunk(CCounter_fracs(ccount));
        //@ steal_fraction( CCounter_fracs (ccount) );
        //@ open CCounter_fracs (ccount)();
        Inc_thread it = new Inc_thread(ccount);  
	(new Thread(it)).start();
        //@ steal_fraction( CCounter_fracs (ccount) );
        //@ open CCounter_fracs (ccount)();
	Inc_thread it2 = new Inc_thread(ccount);  
	(new Thread(it2)).start();
	//@ steal_fraction( CCounter_fracs (ccount) );
        //@ open CCounter_fracs (ccount)();
	Dec_thread it3 = new Dec_thread(ccount);  
	(new Thread(it3)).start();
    }


    public void doMain3 ()
    //@ requires emp;
    //@ ensures emp;
    {
        CCounter ccount = new CCounter();
        //@ close CCounter_fracs (ccount)();
        //@ create_fractionable_chunk(CCounter_fracs(ccount));

        int i = 10;
        while (i>0)
        //@ invariant frac_chunk(CCounter_fracs (ccount),?fr,?nn) &*& fr>0 &*& fr<=1;
        {
        	//@ steal_fraction( CCounter_fracs (ccount) );
        	//@ open [fr/2]CCounter_fracs (ccount)();
        	Inc_thread it = new Inc_thread(ccount);  
		(new Thread(it)).start();
        }
    }




    public static void main(String[] args) 
    //@ requires emp;
    //@ ensures emp;
    {
	new Main().doMain2();
    }

}
