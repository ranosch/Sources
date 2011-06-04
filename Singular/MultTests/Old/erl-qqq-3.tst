LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x(1..6)),dp;
poly F = x(5)*x(2)*x(6)+x(4)*x(6)*x(5)+x(1)*x(6)*x(5)+x(1)*x(2)*x(5)+x(1)*x(4)*x(6)+x(1)*x(4)*x(3)+x(1)*x(6)*x(3)+x(4)*x(2)*x(3)+x(4)*x(6)*x(3)+x(4)*x(2)*x(1)+x(1)*x(2)*x(6)+x(4)*x(2)*x(5)+x(5)*x(3)*x(1)+x(6)*x(3)*x(2)+x(5)*x(2)*x(3)+x(5)*x(4)*x(3);
bfct(F,0,0,1);
tst_status(1);$
