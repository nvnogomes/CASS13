class Counter {
  int N;
  //@ predicate valid(int v) = (this.N |-> v)  &*& (v>=0);
  // INVARIANT valid(?b)

Counter()
//@ requires true;
//@ ensures valid(0);
{
 N = 0;
}

void  inc() 
  //@ requires valid(?b);
  //@ ensures valid(b+1);
  {
  //@ open valid(b);
	N++;
  //@ close valid(_);
  }

void dec() 
  //@ requires valid(?b);
  //@ ensures valid(_);
  { 
  //@ open valid(b);
  if (N>0) N--; 
  //@ close valid(_);
  }

}

