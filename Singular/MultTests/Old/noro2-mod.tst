LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(u,v,w,x,y,z),dp;
poly F = (u * v)^2 + (w * x)^2 + (y * z)^2;
bfct(F);
tst_status(1);$
