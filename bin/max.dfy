/*
 * pos-condition: the bigger will be returned
 */
method max(a: int, b: int) returns (max: int)
ensures ( a >= b ==> max == a ) && ( b >= a ==> max == b ) ;
{
	if( a > b ) {
		max := a;
	}
	else {
		max := b;
	}
}


/*
 * como a verificação é estática
 * este programa não dá erro porque
 * o corpo do if nunca vai ser executado 
 *
 * pre-condition: y <= 10
 */
method test_max(y:int)
requires y <= 10;
{
	var x:int := max(y,10);
	if( x > 10 ) {
		assert x == 3;
	}
	assert x == 10;
}

/*
 * loop invariants
 * loop invariants are also pos-conditions
 * pos-condition: m must be greater than all array members
 * pos-condition: m must be one of the array members
 */
method max_vec( a:array<int> ) returns ( m:int )
requires ( a != null );
requires ( a.Length > 0 );
ensures forall i :: ( 0 <= i < a.Length ) ==> ( m >= a[i] );
ensures exists i :: ( 0 <= i < a.Length ) && ( m == a[i] );
{
	var i:int := 1;
	var tmp:int := a[0];
	while ( i < a.Length ) 
		invariant ( 0 <= i <= a.Length );
		invariant forall j :: ( 0 <= j < i ) ==> ( tmp >= a[j] );
		invariant exists j :: ( 0 <= j < i ) && ( tmp == a[j] );
	{
		if( a[i] > tmp ) {
			tmp := a[i];
		}
		i := i + 1;
	}
	m := tmp;
}


/*
 * returns index j such that a[j] == x or -1 if there is no such
 * invariant: while
 * sendto: luis.caires@di.fct.unl.pt
 */
method find_vec( a:array<int>, x:int) returns (p:int)
requires ( a != null );
requires ( a.Length > 0 );
ensures (p == -1) ==> (forall j :: ( 0 <= j < a.Length ) ==> x != a[j] ) ;
ensures (p == -1) || (( 0 <= p < a.Length ) &&  x == a[p] ) ;
{
	var i:int := 0;
	
	
	while ( i < a.Length ) 
		invariant ( 0 <= i <= a.Length );
		invariant forall j :: (0 < j < i) ==> a[j] != x;
	{
		if( a[i] == x ) {
			p := i;
			return;
		}
		i := i + 1;
	}
	p := -1;
}


/*
 * MAIN BODY
 */
method Main()
{
	test_max(7);
}
