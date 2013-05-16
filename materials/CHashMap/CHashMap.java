package CHashMapMain;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@

predicate_ctor CHashMap_shared_state (CHashMap h) () = h.map |-> ?t &*& t.Map(_) &*& t != null; 

predicate CHashMapInv(CHashMap h;) = 
                  h.rl |-> ?r &*& r!=null &*& rlck(r,1/2,CHashMap_shared_state(h)) &*&
                  h.wl |-> ?w &*& w!=null &*& wlck(w,1,CHashMap_shared_state(h));

@*/

public class CHashMap {

  HashMap map;
  ReentrantReadWriteLock mon;
  ReadLock rl;
  WriteLock wl;

public CHashMap()
//@ requires true;
//@ ensures CHashMapInv(this);
{
  map = new HashMap();
//@ close CHashMap_shared_state(this)();
//@ close enter_rwlck(CHashMap_shared_state(this));
  mon = new ReentrantReadWriteLock();
  rl = mon.readLock();
  wl = mon.writeLock();
//@ close CHashMapInv(this);
}


public Object get(Object key) 
//@ requires [?f]CHashMapInv(this);
//@ ensures [f]CHashMapInv(this);
  {
   Object r;
   //@ open [f]CHashMapInv(this);
   rl.lock(); 
   //@ open [?rf]CHashMap_shared_state(this)();
   r = map.get(key);
   // map.remove(key);
  //@ close [rf]CHashMap_shared_state(this)();
   rl.unlock();
  //@ close [f]CHashMapInv(this);
  return r;
}

public Object wget(Object key) 
//@ requires [?f]CHashMapInv(this);
//@ ensures [f]CHashMapInv(this);
  {
   Object r = null;
   //@ open [f]CHashMapInv(this);
   rl.lock();  // start_read
   //@ open [?rf]CHashMap_shared_state(this)();
   //@ close [rf]CHashMap_shared_state(this)();
   rl.unlock(); // end_read
  //@ close [f]CHashMapInv(this);
  return r;
}

public void remove(Object key)
//@ requires [?f]CHashMapInv(this);
//@ ensures [f]CHashMapInv(this);
{
//@ open [f]CHashMapInv(this);
    wl.lock(); // start_write
//@ open CHashMap_shared_state(this)();
    map.remove(key);
    map.get(key);
//@ close CHashMap_shared_state(this)();
    wl.unlock(); // end_write
//@ close [f]CHashMapInv(this);
}

}

