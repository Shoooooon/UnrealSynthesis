n = 10

def nonint() :
    ### Given Precondition
    condlist = []
    for i in range(-n, n+1):
        condlist.append("(= x[" + str(i) + "] " + str(i) + ")" )

    cond = "true"
    for entry in condlist:
        cond = "(and " + entry + " " + cond + ")"

    print(cond)
    # (and (= x[7] 7) (and (= x[6] 6) (and (= x[5] 5) (and (= x[4] 4) (and (= x[3] 3) (and (= x[2] 2) (and (= x[1] 1) (and (= x[0] 0) (and (= x[-1] -1) (and (= x[-2] -2) (and (= x[-3] -3) (and (= x[-4] -4) (and (= x[-5] -5) (and (= x[-6] -6) (and (= x[-7] -7) true)))))))))))))))

    ### Target Postcondition
    condlist = []
    for i in range(-n, n+1):
        condlist.append("(= x[" + str(i) + "] " + str((pow(-1,n-i)+1)/2) + ")" )

    cond = "true"
    for entry in condlist:
        cond = "(and " + entry + " " + cond + ")"

    print("(not " + cond + ")")
    # (not (and (= x[7] 1) (and (= x[6] 0) (and (= x[5] 1) (and (= x[4] 0) (and (= x[3] 1) (and (= x[2] 0) (and (= x[1] 1) (and (= x[0] 0) (and (= x[-1] 1) (and (= x[-2] 0) (and (= x[-3] 1) (and (= x[-4] 0) (and (= x[-5] 1) (and (= x[-6] 0) (and (= x[-7] 1) true))))))))))))))))

    ### N Summary
    condlist = []
    for i in range(-n, n+1):
        condlist.append("(= e_t[" + str(i) + "] n)" )
    cond = "true"
    for entry in condlist:
        cond = "(and " + entry + " " + cond + ")"

    print("exists ((n Int)) " + cond)

    # exists ((n Int)) (and (= e_t[7] n) (and (= e_t[6] n) (and (= e_t[5] n) (and (= e_t[4] n) (and (= e_t[3] n) (and (= e_t[2] n) (and (= e_t[1] n) (and (= e_t[0] n) (and (= e_t[-1] n) (and (= e_t[-2] n) (and (= e_t[-3] n) (and (= e_t[-4] n) (and (= e_t[-5] n) (and (= e_t[-6] n) (and (= e_t[-7] n) true)))))))))))))))

    ### B Summary
    noboundlist = []
    for i in range(-n, n+1):
        noboundlist.append("b_t[" + str(i) + "]" )
    noboundcond = "true"
    for entry in noboundlist:
        noboundcond = "(and " + entry + " " + noboundcond + ")"

    lowerboundlist = []
    for i in range(-n, n+1):
        lowerboundlist.append("(<-> b_t[" + str(i) + "] (< x[" + str(i) + "] lo))" )
    lowcond = "true"
    for entry in lowerboundlist:
        lowcond = "(and " + entry + " " + lowcond + ")"

    upperboundlist = []
    for i in range(-n, n+1):
        upperboundlist.append("(<-> b_t[" + str(i) + "] (< hi x[" + str(i) + "]))" )
    hicond = "true"
    for entry in upperboundlist:
        hicond = "(and " + entry + " " + hicond + ")"

    doubleboundlist = []
    for i in range(-n, n+1):
        doubleboundlist.append("(<-> b_t[" + str(i) + "] (or (< x[" + str(i) + "] lo) (< hi x[" + str(i) + "])))" )
    doublecond = "true"
    for entry in doubleboundlist:
        doublecond = "(and " + entry + " " + doublecond + ")"

    # print("exists ((hi Int) (lo Int)) (or " + noboundcond + " (or " + lowcond + " (or " + hicond + " " + doublecond + ")))")
    print("exists ((hi Int) (lo Int)) (or " + lowcond + " (or " + hicond + " " + doublecond + "))")

    # exists ((hi Int) (lo Int)) (or (and (<-> b_t[7] (< lo x[7])) (and (<-> b_t[6] (< lo x[6])) (and (<-> b_t[5] (< lo x[5])) (and (<-> b_t[4] (< lo x[4])) (and (<-> b_t[3] (< lo x[3])) (and (<-> b_t[2] (< lo x[2])) (and (<-> b_t[1] (< lo x[1])) (and (<-> b_t[0] (< lo x[0])) (and (<-> b_t[-1] (< lo x[-1])) (and (<-> b_t[-2] (< lo x[-2])) (and (<-> b_t[-3] (< lo x[-3])) (and (<-> b_t[-4] (< lo x[-4])) (and (<-> b_t[-5] (< lo x[-5])) (and (<-> b_t[-6] (< lo x[-6])) (and (<-> b_t[-7] (< lo x[-7])) true))))))))))))))) (or (and (<-> b_t[7] (< x[7] hi)) (and (<-> b_t[6] (< x[6] hi)) (and (<-> b_t[5] (< x[5] hi)) (and (<-> b_t[4] (< x[4] hi)) (and (<-> b_t[3] (< x[3] hi)) (and (<-> b_t[2] (< x[2] hi)) (and (<-> b_t[1] (< x[1] hi)) (and (<-> b_t[0] (< x[0] hi)) (and (<-> b_t[-1] (< x[-1] hi)) (and (<-> b_t[-2] (< x[-2] hi)) (and (<-> b_t[-3] (< x[-3] hi)) (and (<-> b_t[-4] (< x[-4] hi)) (and (<-> b_t[-5] (< x[-5] hi)) (and (<-> b_t[-6] (< x[-6] hi)) (and (<-> b_t[-7] (< x[-7] hi)) true))))))))))))))) (and (<-> b_t[7] (and (< lo x[7]) (< x[7] hi))) (and (<-> b_t[6] (and (< lo x[6]) (< x[6] hi))) (and (<-> b_t[5] (and (< lo x[5]) (< x[5] hi))) (and (<-> b_t[4] (and (< lo x[4]) (< x[4] hi))) (and (<-> b_t[3] (and (< lo x[3]) (< x[3] hi))) (and (<-> b_t[2] (and (< lo x[2]) (< x[2] hi))) (and (<-> b_t[1] (and (< lo x[1]) (< x[1] hi))) (and (<-> b_t[0] (and (< lo x[0]) (< x[0] hi))) (and (<-> b_t[-1] (and (< lo x[-1]) (< x[-1] hi))) (and (<-> b_t[-2] (and (< lo x[-2]) (< x[-2] hi))) (and (<-> b_t[-3] (and (< lo x[-3]) (< x[-3] hi))) (and (<-> b_t[-4] (and (< lo x[-4]) (< x[-4] hi))) (and (<-> b_t[-5] (and (< lo x[-5]) (< x[-5] hi))) (and (<-> b_t[-6] (and (< lo x[-6]) (< x[-6] hi))) (and (<-> b_t[-7] (and (< lo x[-7]) (< x[-7] hi))) true)))))))))))))))))
    # exists ((hi Int) (lo Int)) (or (and b_t[7] (and b_t[6] (and b_t[5] (and b_t[4] (and b_t[3] (and b_t[2] (and b_t[1] (and b_t[0] (and b_t[-1] (and b_t[-2] (and b_t[-3] (and b_t[-4] (and b_t[-5] (and b_t[-6] (and b_t[-7] true))))))))))))))) (or (and (<-> b_t[7] (< x[7] lo)) (and (<-> b_t[6] (< x[6] lo)) (and (<-> b_t[5] (< x[5] lo)) (and (<-> b_t[4] (< x[4] lo)) (and (<-> b_t[3] (< x[3] lo)) (and (<-> b_t[2] (< x[2] lo)) (and (<-> b_t[1] (< x[1] lo)) (and (<-> b_t[0] (< x[0] lo)) (and (<-> b_t[-1] (< x[-1] lo)) (and (<-> b_t[-2] (< x[-2] lo)) (and (<-> b_t[-3] (< x[-3] lo)) (and (<-> b_t[-4] (< x[-4] lo)) (and (<-> b_t[-5] (< x[-5] lo)) (and (<-> b_t[-6] (< x[-6] lo)) (and (<-> b_t[-7] (< x[-7] lo)) true))))))))))))))) (or (and (<-> b_t[7] (< hi x[7])) (and (<-> b_t[6] (< hi x[6])) (and (<-> b_t[5] (< hi x[5])) (and (<-> b_t[4] (< hi x[4])) (and (<-> b_t[3] (< hi x[3])) (and (<-> b_t[2] (< hi x[2])) (and (<-> b_t[1] (< hi x[1])) (and (<-> b_t[0] (< hi x[0])) (and (<-> b_t[-1] (< hi x[-1])) (and (<-> b_t[-2] (< hi x[-2])) (and (<-> b_t[-3] (< hi x[-3])) (and (<-> b_t[-4] (< hi x[-4])) (and (<-> b_t[-5] (< hi x[-5])) (and (<-> b_t[-6] (< hi x[-6])) (and (<-> b_t[-7] (< hi x[-7])) true))))))))))))))) (and (<-> b_t[7] (or (< x[7] lo) (< hi x[7]))) (and (<-> b_t[6] (or (< x[6] lo) (< hi x[6]))) (and (<-> b_t[5] (or (< x[5] lo) (< hi x[5]))) (and (<-> b_t[4] (or (< x[4] lo) (< hi x[4]))) (and (<-> b_t[3] (or (< x[3] lo) (< hi x[3]))) (and (<-> b_t[2] (or (< x[2] lo) (< hi x[2]))) (and (<-> b_t[1] (or (< x[1] lo) (< hi x[1]))) (and (<-> b_t[0] (or (< x[0] lo) (< hi x[0]))) (and (<-> b_t[-1] (or (< x[-1] lo) (< hi x[-1]))) (and (<-> b_t[-2] (or (< x[-2] lo) (< hi x[-2]))) (and (<-> b_t[-3] (or (< x[-3] lo) (< hi x[-3]))) (and (<-> b_t[-4] (or (< x[-4] lo) (< hi x[-4]))) (and (<-> b_t[-5] (or (< x[-5] lo) (< hi x[-5]))) (and (<-> b_t[-6] (or (< x[-6] lo) (< hi x[-6]))) (and (<-> b_t[-7] (or (< x[-7] lo) (< hi x[-7]))) true))))))))))))))))))

def single_sided():
    ### Given Precondition
    condlist = []
    for i in range(0, n+1):
        condlist.append("(= x[" + str(i) + "] " + str(i) + ")" )

    cond = "true"
    for entry in condlist:
        cond = "(and " + entry + " " + cond + ")"

    print(cond)
    
    ### Target Postcondition
    condlist = []
    for i in range(0, n+1):
        condlist.append("(= x[" + str(i) + "] " + str((pow(-1,n-i)+1)/2) + ")" )

    cond = "true"
    for entry in condlist:
        cond = "(and " + entry + " " + cond + ")"

    print("(not " + cond + ")")
    
    ### N Summary
    condlist = []
    for i in range(0, n+1):
        condlist.append("(= e_t[" + str(i) + "] n)" )
    cond = "true"
    for entry in condlist:
        cond = "(and " + entry + " " + cond + ")"

    print("exists ((n Int)) " + cond)

    ### B Summary
    lowerboundlist = []
    for i in range(0, n+1):
        lowerboundlist.append("(<-> b_t[" + str(i) + "] (< x[" + str(i) + "] lo))" )
    lowcond = "true"
    for entry in lowerboundlist:
        lowcond = "(and " + entry + " " + lowcond + ")"

    print("exists ((lo Int)) " + lowcond)

single_sided()