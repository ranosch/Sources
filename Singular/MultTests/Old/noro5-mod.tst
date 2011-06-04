LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(u,v,w,x,y,z),dp;
poly F = (u * v)^5 + (w * x)^5 + (y * z)^5;
bfct(F);
tst_status(1);$
