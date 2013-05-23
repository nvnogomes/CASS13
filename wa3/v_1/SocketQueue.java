import java.net.Socket;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;


// Bounded Queue Representation Invariant
// I expose in the invariant the number of elements in the Queue
// and the upper bound on elements

/*@
predicate_ctor shared_state (SocketQueue sq) () = 
  sq.numOfElements |-> ?v &*&
  v >= 0 ;

predicate_ctor notEmpty_state (SocketQueue sq) () = 
  sq.numOfElements |-> ?v &*&
  v > 0 ;

predicate_ctor notFull_state (SocketQueue sq) () = 
  sq.numOfElements |-> ?v &*&
  v < maxCapacity ;


predicate QueueInv(int n, int m) = 
  this.store |-> ?s &*&
  this.maxCapacity |-> m &*&
  this.numOfElements |-> n &*&
  this.head |-> ?h &*& 
  this.tail |-> ?t &*& 
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
  this.mutex |-> ?l &*&
  l != null &*&
  lck(l,1,shared_state(this)) &*&
  this.notEmpty |-> ?cce &*& 
  cce !=null &*& 
  cond(cce,shared_state(this), notEmpty_state(this)) &*&
  this.notFull |-> ?ccf &*& 
  ccf !=null &*& 
  cond(ccf,shared_state(this), notFull_state(this));
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
	// @ requires size > 0;
	// @ ensures QueueInv(0,size);
	{
		maxCapacity = size;
		store = new Socket[size + 1];
		numOfElements = 0;
		head = tail = 0;
		
		mutex = new ReentrantLock(true);
		notEmpty = mutex.newCondition();
		notFull = mutex.newCondition();
	}

	public int getNumOfElements()
	// @ requires QueueInv(?n,?m);
	// @ ensures QueueInv(n,m) &*& result == n &*& n<=m;
	{
		return numOfElements;
	}

	public void enqueue(Socket socketElem)
	// @ requires QueueInv(?n,?m) &*& n<m;
	// @ ensures QueueInv(n+1,m);
	{
		mutex.lock();
		try {
			if (numOfElements == maxCapacity) {
				notFull.await();
			}

			store[tail] = socketElem;
			tail = ++tail % maxCapacity;
			numOfElements++;
			notEmpty.signal();
		} catch (Exception e) {} 
//		finally {
			mutex.unlock();
//		}
	}

	public Socket dequeue()
	// @ requires QueueInv(?n,?m) &*& n>0;
	// @ ensures QueueInv(n-1,m) ;
	{
		Socket socketElem = null;
		try {
			mutex.lock();
			if (numOfElements == 0) {
				notEmpty.await();
			}

			socketElem = store[head];
			head = ++head % maxCapacity;
			numOfElements--;
			notFull.signal();

		} catch (Exception e) {} 
//		finally {
			mutex.unlock();
//		}

		return socketElem;
	}
}
