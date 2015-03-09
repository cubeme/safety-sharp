procedure F(n: int) returns (r: int);
  ensures 100 < n ==> r == n - 10;
  ensures n <= 100 ==> r == 91;



implementation F(n: int) returns (r: int)
{
  /*** structured program:
    if (100 < n)
    {
        r := n - 10;
    }
    else
    {
        call r := F(n + 11);
        call r := F(r);
    }
  **** end structured program */
  anon0:
    goto anon3_Then, anon3_Else;

  anon3_Then:
    assume {:partition} 100 < n;
    r := n - 10;
    return;

  anon3_Else:
    assume {:partition} n <= 100;
    call r := F(n + 11);
    call r := F(r);
    return;
}