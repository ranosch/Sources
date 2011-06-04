LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = x*y*z*(x+y)*(x+z); 
bfct(F);
tst_status(1);$

