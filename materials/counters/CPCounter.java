import java.util.concurrent.*;
import java.util.concurrent.locks.*;

public class CPCounter {

  int N;
  ReentrantLock mon;
  Condition notzero; 

public CPCounter()
{
 N = 0;
 mon = new ReentrantLock();
notzero = mon.newCondition();
}

public int get()
{
return N;
}

public void inc() 
  {
  mon.lock();
   N++;
   notzero.signal();
   mon.unlock();
  }

public void dec()
{
  try {
  mon.lock();
  if (N==0) {
  notzero.await();
  N--;
  }
  } catch (java.lang.InterruptedException e){} 
    mon.unlock();
  } 
}
