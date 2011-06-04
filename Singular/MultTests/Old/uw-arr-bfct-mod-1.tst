LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = -x*y^3*z+x*y*z^3;
bfct(F);
tst_status(1);$
