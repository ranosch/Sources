LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F =x^6*z-x*y^5*z+x^5*y-y^6; 
bfct(F);
tst_status(1);$

