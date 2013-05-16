/*
 * CASS
 * First Handout - Dafny
 */

function IsString( a:array<int> ):bool
  reads a;
{
 a != null &&
 a.Length > 0 &&
 a[0] >= 0 &&
 a[0] < a.Length &&
 forall i :: (1<=i<=a[0]) ==> 0<=a[i]<=255
}


/*
 * returns the length of string a
 * pre: a is a tagged string
 * pos: l is non negative
 * pos: l is the length of a
 */
method tstrlen( a:array<int> ) returns ( l:int )
  requires IsString( a ) ;
  ensures l >= 0 ;
  ensures l == a[0] + 1 ;
{
  l := a[0] ;
}

/*
 * returns a copy of string a
 */
method tstrcpy( a:array<int> ) returns ( b:array<int> )
  requires IsString( a ) ;
  ensures IsString( b ) ;
  ensures forall i :: ( 1<= i <= a[0] ) ==> a[i] == b[i] ;
{
  b := new int[ a.Length + 1 ] ;
  b[0] := a[0] ;

  var i:int := 1 ;
  while( i < a[0] )
    invariant 1 <= i <= a[0] + 1 ;
    invariant forall k :: ( 1 <= k < i ==> a[k] == b[k] ) ;
  {
    b[i] := a[i] ;
    i := i + 1 ;
  }
}

/*
 * returns the concatenation of strings a and b as a string c
 */
method tstrcat( a:array<int>, b:array<int> ) returns ( c:array<int> )
  requires IsString( a ) ;
  requires IsString( b ) ;
  requires b != null && b.Length > 0 ;
  ensures c.Length > a.Length + b.Length;
{
  c := new int[ a[0] + b[0] + 1 ] ;
  c[0] := a.Length + b.Length ;
  var i:int := 1 ;

  while( i <= c[0] )
    // invariant 1 <= i <= c.Length ;
  {
    if( i <= a[0] )
    {
      c[i] := a[i] ;
    }
    else
    {
      var index:int := i - a[0] ;
      var bi:int := b[ 0 ] ;
      //c[i] := b[ index ] ;
      print i - a[1] ;
    }

    i := i + 1 ;
  }

  return c ;
}



/*
 * MAIN method
 */
method Main()
{
  var a := new int[4]; // 3 element array of ints
  a[0], a[1], a[2], a[3] := 3, 1, 2, 3;

  var b := new int[5]; // 3 element array of ints
  b[0], b[1], b[2], b[3], b[4] := 4, 4, 5, 6, 7;


  var c := tstrcat(a, b);
  print c;

}
