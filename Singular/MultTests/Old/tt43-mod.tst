LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
int n = 4;
int m = 3;
poly F = x^n + y^n + z^n - (x*y*z)^m; 
bfct(F);
tst_status(1);$

