LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z,w),dp;
poly F = x*y*z*w*(x+w)*(y+w)*(z+w);
bfct(F);
tst_status(1);$
