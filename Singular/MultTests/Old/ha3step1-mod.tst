LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z,w),dp;
poly F = x*y*z*w*(x+y)*(x+z)*(x+w)*(y+z+w); 
bfct(F);
tst_status(1);$

