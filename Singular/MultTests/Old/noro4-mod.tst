LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(u,v,w,x,y,z),dp;
poly F = (u * v)^4 + (w * x)^4 + (y * z)^4;
bfct(F);
tst_status(1);$
