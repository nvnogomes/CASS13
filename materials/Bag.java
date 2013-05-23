
public class Bag  {

	int store[];
	int nelems;

	/*@
		predicate BagInv() =
			store |-> ?s &*&
			nelems |-> ?n &*&
			s != null &*&
			n >= 0 &*&
			n <= s.length &*&
			array_slice(s, 0, s.length,_);
	 @*/


	public Bag(int size)
		//@ requires size >= 0;
		//@ ensures BagInv();
	{
		store = new int[size];
		nelems = 0;
	}

	public boolean add(int v)
		//@ requires BagInv();
		//@ ensures BagInv();
	{
		if(nelems < store.length) {
			store[nelems] = v;
			nelems++;
			return true;
		}
		else {
			return false;
		}
	}

	public int size()
		//@ requires BagInv();
		//@ ensures BagInv() &*& result >= 0;
	{
		return nelems;
	}

}
