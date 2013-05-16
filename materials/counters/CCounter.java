import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@

predicate_ctor CCounter_shared_state (CCounter c) () = c.N |-> ?v &*& v >= 0; 
predicate_ctor CCounter_nonzero (CCounter c) () = c.N |-> ?v &*& v > 0; 

predicate inv(CCounter c) =  
     c.mon |-> ?l &*& l!=null &*& lck(l,1,CCounter_shared_state(c))
 &*& c.notzero |-> ?cc &*& cc !=null &*& cond(cc,CCounter_shared_state(c),CCounter_nonzero(c));

@*/

public class CCounter {

  int N;
  ReentrantLock mon;
  Condition notzero; 

public CCounter()
//@ requires true;
//@ ensures inv(this);
{
//@ close CCounter_shared_state(this)();
//@ close enter_lck(1,CCounter_shared_state(this));
 mon = new ReentrantLock();
 //@ close set_cond(CCounter_shared_state(this),CCounter_nonzero(this));  
notzero = mon.newCondition();
//@ close inv(this);
}

public void inc() 
//@ requires inv(this);
//@ ensures inv(this);
  {
  //@ open inv(this);
  mon.lock();
  //@ open CCounter_shared_state(this)();
   N++;
  //@ close CCounter_nonzero(this)();
   notzero.signal();
   mon.unlock();
  //@ close inv(this);
  }

public void dec()
//@ requires inv(this);
//@ ensures inv(this);
{
  try {
//@ open inv(this);
  mon.lock();
//@ open CCounter_shared_state(this)();
  if (N==0) {
//@ close CCounter_shared_state(this)();
  notzero.await();
//@ open CCounter_nonzero(this)();
  N--;
  }
  } catch (java.lang.InterruptedException e){} 
//@ close CCounter_shared_state(this)();
    mon.unlock();
//@ close inv(this);
  } 
}
