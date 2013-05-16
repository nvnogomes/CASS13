public class Queue {

    int store[];
    int max;
    int nelms;
    int hd;
    int tl;

    //  Bounded Queue Representation Invariant
    //  I expose in the invariant the number of elements in the Queue
    //  and the upper bound on elements

    /*@ predicate Queue(int n, int m) =
          this.store |-> ?s
      &*& this.max |-> m
      &*& this.nelms |-> n
      &*& this.hd |-> ?h
      &*& this.tl |-> ?t
      &*& s != null
      &*& 0 <= m &*& m<s.length &*& array_slice(s,0,m,_)
      &*& 0 <= n &*& n<=m
      &*& 0 <= h &*& h <m
      &*& 0 <= t &*& t <m
      &*& (h<t ? n==t-h : true)
      &*& (h==t ? (n==m||n==0) : true)
      &*& (h>t ? n==t+(m-h) : true);
      @*/

    Queue(int size)
    //@ requires size > 0;
    //@ ensures Queue(0,size);
    {
	max = size;
	store = new int[size+1];
	nelms = 0;
	hd = tl = 0;
    }
    
    int getnelms()
    //@ requires Queue(?n,?m);
    //@ ensures Queue(n,m) &*& result == n &*& n<=m;
    {
	return nelms;
    }
    
    void enqueue(int v)
    //@ requires Queue(?n,?m) &*& n<m;
    //@ ensures Queue(n+1,m);
    {
          store[tl] = v;
          tl++;
          nelms++;
          if(tl==max) tl = 0;
    }

    int dequeue()
    //@ requires Queue(?n,?m) &*& n>0;
    //@ ensures Queue(n-1,m) ;
    {
      int v = store[hd];
      hd++;
      nelms--;
      if(hd==max) hd = 0;
      return v;
    }

    static void test(Queue q0)
    //@ requires q0.Queue(_,_);
    //@ ensures true;
    {
    Queue q1 = new Queue(10);
    q1.enqueue(0);
    if(q0.getnelms()>0) q0.dequeue();
    q1.dequeue();
    }
}
