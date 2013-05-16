class OSET {

	var nelems:int ;
	var gset:set<T> ;

	/*
	 * OSET invariant
	 */
	function inv():bool
		reads this;
	{
		elems >= 0 && gset != null
	}


	/* { this == s }
	 * { this == s U {n} }
	 */
	method insert(n:int)
		requires inv();
		ensures inv();
	{
		gset := gset + {n} ;
	}


	/* 	{ this == s }
	 *	{ this == s \ {n} }
	 */
	method delete(n:int)
		requires inv() ;
		ensures inv() ;
		ensures n !in gset ;
	{
		gset := gset + {n} ;
	}


	/*  { this == s }
	 *	{result = ( n ∊ s } }
	 */
	method contains(n:int) returns (r:bool)
		requires inv();
		ensures inv();
	{
		r := n in gset;
	}


	/* { this == s && #s>0 }
	 * { result ∊ s && forall x. x ∊ s => (result >= x) }
	 */
	method max() returns (r:int)
		requires inv();
		requires nelems > 0 ;
		ensures inv();
	{

	}


	/* { this == s && #s>0 }
	 * { result ∊ s && forall x. x ∊ s => (result <= x) }
	 */
	method min() returns (r:int)
		requires inv();
		requires nelems > 0 ;
		ensures inv();
	{

	}


} /*end class*/
