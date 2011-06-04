LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(u,v,w,x,y,z),dp;
poly F = (u * v)^3 + (w * x)^3 + (y * z)^3;
bfct(F);
tst_status(1);$
