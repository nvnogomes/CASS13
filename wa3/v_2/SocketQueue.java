import java.net.Socket;
import java.util.concurrent.locks.*;


/*@
predicate_ctor shared_state (SocketQueue sq) () = 
  sq.numOfElements |-> ?v &*&
  v >= 0 ;

predicate_ctor notEmpty_state (SocketQueue sq) () = 
  sq.numOfElements |-> ?v &*&
  v > 0 ;

predicate_ctor notFull_state (SocketQueue sq) () = 
  sq.numOfElements |-> ?v &*&
  v < sq.maxCapacity ;


predicate QueueInv(SocketQueue q, int n, int m) = 
  q.store |-> ?s &*&
  q.maxCapacity |-> m &*&
  q.numOfElements |-> n &*&
  q.head |-> ?h &*& 
  q.tail |-> ?t &*& 
  s != null &*& 
  0 <= m &*& 
  m < s.length &*&
  array_slice(s,0,m,_) &*&
  0 <= n 
  &*& 
  n <= m &*& 
  0 <= h &*&
  h <m &*& 
  0 <= t &*& 
  t <m &*& 
  (h < t ? n == t-h : true) &*&
  (h==t ? ( n==m|| n==0) : true) &*& 
  (h>t ? n==t+(m-h) : true) &*&
  q.mutex |-> ?l &*&
  l != null &*&
  lck(l,1,shared_state(q)) &*&
  q.notEmpty |-> ?cce &*& 
  cce !=null &*& 
  cond(cce,shared_state(q), notEmpty_state(q)) &*&
  q.notFull |-> ?ccf &*& 
  ccf !=null &*& 
  cond(ccf,shared_state(q), notFull_state(q));
 @*/


public class SocketQueue {

	Socket[] store;
	int maxCapacity;
	int numOfElements;
	int head;
	int tail;
	
	// concurrency
	ReentrantLock mutex;
	Condition notEmpty, notFull;



	public SocketQueue(int size)
	//@ requires size > 0;
	//@ ensures QueueInv(this, 0, size);
	{
		if( size < 40 ) {
			maxCapacity = size;
			store = new Socket[size + 1];
			numOfElements = 0;
			head = tail = 0;
		
			//@ close shared_state(this)();
			//@ close enter_lck(1,shared_state(this));
			mutex = new ReentrantLock();
			//@ close set_cond(shared_state(this),notEmpty_state(this));  
			notEmpty = mutex.newCondition();
			//@ close set_cond(shared_state(this),notFull_state(this));  
			notFull = mutex.newCondition();
			//@ close QueueInv(this, 0, size);
		}
		else {
			System.err.println("Max workers: 40");
			System.exit(1);
		}

	}

	public int getNumOfElements()
	//@ requires QueueInv(this, ?n, ?m);
	//@ ensures QueueInv(this, n, m) &*& result == n &*& n < m;
	{
		return numOfElements;
	}

	public void enqueue(Socket socketElem)
	//@ requires QueueInv(this, ?n,?m) &*& n<m;
	//@ ensures QueueInv(this, n+1,m);
	{
		//@ open QueueInv(this,n,m);
		mutex.lock();
		//@ open shared_state(this);
		try {
			if (numOfElements == maxCapacity) {
				notFull.await();
				//@ open notFull_state(this)();
			}

			store[tail] = socketElem;
			tail = ++tail % maxCapacity;
			numOfElements++;
			//@ close notEmpty_state(this)();
			notEmpty.signal();
		} catch (Exception e) {} 
//		finally {
			mutex.unlock();
			//@ close QueueInv(this, n, m);
//		}
	}

	public Socket dequeue()
	//@ requires QueueInv(this, ?n,?m) &*& n>0;
	//@ ensures QueueInv(this, n-1,m) ;
	{
		Socket socketElem = null;
		try {
			//@ open shared_state(this);
			mutex.lock();
			if (numOfElements == 0) {
				notEmpty.await();
				//@ open notEmpty_state(this)();
			}

			socketElem = store[head];
			head = ++head % maxCapacity;
			numOfElements--;
			//@ close notFull_state(this)();
			notFull.signal();

		} catch (Exception e) {} 
//		finally {
			mutex.unlock();
			//@ close QueueInv(this);
//		}

		return socketElem;
	}
}
