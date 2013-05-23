package CCounterMain;

import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@

predicate_ctor CCounter_shared_state (CCounter c) () = c.N |-> ?v &*& v >= 0 ;

predicate_ctor CCounter_notzero_state (CCounter c) () = c.N |-> ?v &*& v > 0 ;

predicate CCounterInv(CCounter c;) =  
   c.mon |-> ?l 
   &*& l!=null 
   &*& lck(l,1,CCounter_shared_state(c))
   &*& c.notzero |-> ?cc
   &*& cc !=null 
   &*& cond(cc,CCounter_shared_state(c),CCounter_notzero_state(c));
  
@*/

public class CCounter {

  int N;
  ReentrantLock mon;
  Condition notzero; 

public CCounter()
//@ requires emp;
//@ ensures CCounterInv(this);
{
//@ close CCounter_shared_state(this)();
//@ close enter_lck(1,CCounter_shared_state(this));
 mon = new ReentrantLock();
 //@ close set_cond(CCounter_shared_state(this),CCounter_notzero_state(this));  
notzero = mon.newCondition();
//@ close CCounterInv(this);
}


public void inc() 
//@ requires [?f]CCounterInv(this);
//@ ensures [f]CCounterInv(this);
  {
  //@ open [f]CCounterInv(this);
   mon.lock();
  //@ open CCounter_shared_state(this)();
   N++;
   //@ close CCounter_notzero_state(this)();
   notzero.signal();
   mon.unlock();
  //@ close [f]CCounterInv(this);
  }

public void dec()
//@ requires [?f]CCounterInv(this);
//@ ensures [f]CCounterInv(this);
{
  try {
//@ open [f]CCounterInv(this);
    mon.lock();
//@ open CCounter_shared_state(this)();
    if (N==0) {
//@ close CCounter_shared_state(this)();
    notzero.await();
//@ open CCounter_notzero_state(this)();
    }
    N--;
  } catch (java.lang.InterruptedException e){} 
//@ close CCounter_shared_state(this)();
    mon.unlock();
//@ close [f]CCounterInv(this);
  } 
}
