
    LIB "tst.lib";
    tst_init();
    ring MYRINGNAME=32003,(u0, u1, u2, u3, u4),lp;
    ideal MYIDEALNAME=u0+2*u1+2*u2+2*u3+2*u4-1,
2*u1*u2+2*u0*u3+2*u1*u4-u3,
u1^2+2*u0*u2+2*u1*u3+2*u2*u4-u2,
2*u0*u1+2*u1*u2+2*u2*u3+2*u3*u4-u1,
u0^2+2*u1^2+2*u2^2+2*u3^2+2*u4^2-u0;
    option(redSB);
    slimgb(MYIDEALNAME);
    kill MYRINGNAME;
    tst_status(1);$
    
