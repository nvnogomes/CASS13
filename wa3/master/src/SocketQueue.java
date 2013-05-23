import java.net.Socket;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

public class SocketQueue {

	Socket[] store;
	int maxCapacity;
	int numOfElements;
	int head;
	int tail;
	ReentrantLock mutex;
	Condition notEmpty, notFull;

	// Bounded Queue Representation Invariant
	// I expose in the invariant the number of elements in the Queue
	// and the upper bound on elements

	/*
	 * @ predicate Queue(int n, int m) = this.store |-> ?s &*& this.max |-> m
	 * &*& this.nelms |-> n &*& this.hd |-> ?h &*& this.tl |-> ?t &*& s != null
	 * &*& 0 <= m &*& m<s.length &*& array_slice(s,0,m,_) &*& 0 <= n &*& n<=m
	 * &*& 0 <= h &*& h <m &*& 0 <= t &*& t <m &*& (h<t ? n==t-h : true) &*&
	 * (h==t ? (n==m||n==0) : true) &*& (h>t ? n==t+(m-h) : true);
	 * 
	 * @
	 */

	public SocketQueue(int size)
	// @ requires size > 0;
	// @ ensures Queue(0,size);
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
	// @ requires Queue(?n,?m);
	// @ ensures Queue(n,m) &*& result == n &*& n<=m;
	{
		return numOfElements;
	}

	public void enqueue(Socket socketElem)
	// @ requires Queue(?n,?m) &*& n<m;
	// @ ensures Queue(n+1,m);
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
		} catch (Exception e) {
		} finally {
			mutex.unlock();
		}
	}

	public Socket dequeue()
	// @ requires Queue(?n,?m) &*& n>0;
	// @ ensures Queue(n-1,m) ;
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

		} catch (Exception e) {
		} finally {
			mutex.unlock();
		}

		return socketElem;
	}

	static void test(SocketQueue q0)
	// @ requires q0.Queue(_,_);
	// @ ensures true;
	{
		SocketQueue q1 = new SocketQueue(10);
		q1.enqueue(new Socket());
		if (q0.getNumOfElements() > 0)
			q0.dequeue();
		q1.dequeue();
	}
}
