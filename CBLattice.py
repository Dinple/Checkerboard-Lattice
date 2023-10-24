import numpy as np
import re

constraint_idx = 0


class CheckerBoard:
    def __init__(self, n_dim_, n_act_):
        global constraint_idx
        constraint_idx = 0
        self.n_dim_ = n_dim_
        self.board = np.zeros((n_dim_, n_dim_), dtype=int)
        self.board[::2, 1::2] = 1
        self.board[1::2, ::2] = 1

        self.num_qbits_ = np.where(self.board == 1)[0].shape[0]

        # NOTE: initial state is not included in the number of actions
        self.n_act = n_act_ + 1

        self.n_ql_rod = n_dim_ * 2 - 1
        self.n_rl_rod = n_dim_ - 1
        self.n_cl_rod = n_dim_ - 1

        # board variables
        self.qbit_act_var_dict = {}
        self.qbit_map_m_var_dict = {}
        self.m_var_dict = {}
        self.QL_var_dict = {}
        self.RL_var_dict = {}
        self.CL_var_dict = {}

        # abstract variables
        self.time_var_dict = {}
        self.entropy_var_dict = {}

        # objective variables
        self.obj_var_dict = {}

    def print_lattice(self, qbit_map_m_var_dict_=None):
        if qbit_map_m_var_dict_ is None:
            # print the index of the qubits on the board and leave the rest as 'x'abs
            qbit_idx = 0
            for i in range(self.n_dim_):
                for j in range(self.n_dim_):
                    if self.board[i][j] == 1:
                        print(" {} ".format(qbit_idx), end="")
                        qbit_idx += 1
                    else:
                        print(" x ", end="")
                print()

        else:
            # qbit_mapping is qbit_map_m_var_dict
            # use regex to extract the row and column number as well as the qbit number
            qbit_mapping = np.ones((self.n_dim_, self.n_dim_), dtype=int) * -1
            for qbit_map in qbit_map_m_var_dict_:
                if qbit_map_m_var_dict_[qbit_map] == False:
                    continue
                # extract the row and column number as well as the qbit number
                row_col_qbit = re.findall(r"\d+", qbit_map)
                row = int(row_col_qbit[1])
                col = int(row_col_qbit[2])
                qbit = int(row_col_qbit[0])
                print("row: {}, col: {}, qbit: {}".format(row, col, qbit))
                qbit_mapping[row][col] = qbit

            # print the qbit mapping
            for i in range(self.n_dim_):
                for j in range(self.n_dim_):
                    if qbit_mapping[i][j] != -1:
                        print(" {} ".format(qbit_mapping[i][j]), end="")
                    else:
                        print(" x ", end="")
                print()

    def preface(self, file):
        file.write("; ====== 0. Preface ======\n")
        file.write("(set-option :smt.core.minimize true)\n")
        file.write("(set-option :produce-models true)\n")
        file.write("(set-option :produce-unsat-cores true)\n")

    def collect_var(self):
        qbit_idx = 0
        for i in range(self.n_dim_):
            # file.write("; row {}\n".format(i))
            for j in range(self.n_dim_):

                def qbit_map_func_init(t):
                    # for each entry in the board, map to a qbit
                    for nqb in range(self.num_qbits_):
                        self.qbit_map_m_var_dict[
                            "qbit_{}_ON_m_r{}_c{}_t{}".format(nqb, i, j, t)
                        ] = False

                self.loop_timestamp_helper(qbit_map_func_init)

                # declare qbit variables
                if self.board[i][j] == 1:
                    # each qbit is map to action (left, right, back, front, diag_up, diag_down) at time t
                    def qbit_func(t):
                        self.qbit_act_var_dict[
                            "qbit_{}_L_t{}".format(qbit_idx, t)
                        ] = False
                        self.qbit_act_var_dict[
                            "qbit_{}_R_t{}".format(qbit_idx, t)
                        ] = False
                        self.qbit_act_var_dict[
                            "qbit_{}_B_t{}".format(qbit_idx, t)
                        ] = False
                        self.qbit_act_var_dict[
                            "qbit_{}_F_t{}".format(qbit_idx, t)
                        ] = False
                        self.qbit_act_var_dict[
                            "qbit_{}_DU_t{}".format(qbit_idx, t)
                        ] = False
                        self.qbit_act_var_dict[
                            "qbit_{}_DD_t{}".format(qbit_idx, t)
                        ] = False

                    self.loop_timestamp_helper(qbit_func)

                    # declare entries of the matrix mapping to qbit
                    def qbit_map_func(t):
                        self.qbit_map_m_var_dict[
                            "qbit_{}_ON_m_r{}_c{}_t{}".format(qbit_idx, i, j, t)
                        ] = True

                    self.loop_timestamp_helper(qbit_map_func)

                    # increment qbit index
                    qbit_idx += 1

                    # if being utilized
                    # self.m_var_dict["m_r{}_c{}_t{}".format(i, j, 1)] = True
                    def m_func_t(t):
                        self.m_var_dict["m_r{}_c{}_t{}".format(i, j, t)] = True

                    self.loop_timestamp_helper(m_func_t)
                else:
                    # declare entries of the matrix
                    # self.m_var_dict["m_r{}_c{}_t{}".format(i, j, 1)] = False
                    def m_func_f(t):
                        self.m_var_dict["m_r{}_c{}_t{}".format(i, j, t)] = False

                    self.loop_timestamp_helper(m_func_f)

        for i in range(self.n_ql_rod):
            # declare control rod QL variables
            def ql_func(t):
                self.QL_var_dict["QL_{}_t{}".format(i, t)] = 1

            self.loop_timestamp_helper(ql_func)

        for i in range(self.n_rl_rod):
            # declare gate RL variables
            def rl_func(t):
                self.RL_var_dict["RL_{}_t{}".format(i, t)] = True

            self.loop_timestamp_helper(rl_func)

        for i in range(self.n_cl_rod):
            # declare gate CL variables
            def cl_func(t):
                self.CL_var_dict["CL_{}_t{}".format(i, t)] = True

            self.loop_timestamp_helper(cl_func)

    def collect_abstract_var(self):
        # time variables
        def time_func(t):
            self.time_var_dict["TIMESTAMP_t{}".format(t)] = False

        self.loop_timestamp_helper(time_func)

        # set the initial time to be true
        self.time_var_dict["TIMESTAMP_t0"] = True

        # objective variables: time taken
        self.obj_var_dict["TOTAL_TIME_TAKEN"] = 0

        # entropy variables: measure if the qbits is moved or not
        def entropy_func(t):
            for nqb in range(self.num_qbits_):
                self.entropy_var_dict["ENTROPY_qbit_{}_t{}".format(nqb, t)] = False

        self.loop_timestamp_helper(entropy_func)

    def loop_timestamp_helper(self, func, before_last=False, skip_first=False):
        for t in range(self.n_act):
            if skip_first:
                if t == 0:
                    continue
            # if before_last is True, then stop at the second last timestamp
            if before_last:
                if t == self.n_act - 1:
                    break
            func(t)

    def get_by_timestamp_helper(self, var_dict, t):
        res = {}
        for var in var_dict:
            if var[-2:] == "t{}".format(t):
                res[var] = var_dict[var]
        return res

    def declare_var_helper(self, var_dict, file):
        # check type of var_dict (boolean or int)
        if type(list(var_dict.values())[0]) == bool:
            for var in var_dict:
                file.write("(declare-const {} Bool)\n".format(var))
        elif type(list(var_dict.values())[0]) == int:
            for var in var_dict:
                file.write("(declare-const {} Int)\n".format(var))

    def assert_var_helper(self, var_dict, file, init_t=True):
        global constraint_idx
        # check type of var_dict (boolean or int)
        if type(list(var_dict.values())[0]) == bool:
            for var in var_dict:
                if init_t and var[-3:] == "_t0":
                    file.write(
                        "(assert (! (= {} {}) :named c{}))\n".format(
                            var, str(var_dict[var]).lower(), constraint_idx
                        )
                    )
                    constraint_idx += 1
                else:
                    pass
        elif type(list(var_dict.values())[0]) == int:
            for var in var_dict:
                if init_t and var[-3:] == "_t0":
                    file.write(
                        "(assert (! (= {} {}) :named c{}))\n".format(
                            var, var_dict[var], constraint_idx
                        )
                    )
                    constraint_idx += 1
                else:
                    pass

    def declare_var(self, file):
        # declare all the variables
        file.write("; ====== A. Declare Variables ======\n")
        file.write("; A.1) Q-Bit Vars\n")
        self.declare_var_helper(self.qbit_act_var_dict, file)
        file.write("; A.2) Q-Bit Map Matrix Vars\n")
        self.declare_var_helper(self.qbit_map_m_var_dict, file)
        file.write("; A.3) Matrix Vars\n")
        self.declare_var_helper(self.m_var_dict, file)
        file.write("; A.4) QL Vars\n")
        self.declare_var_helper(self.QL_var_dict, file)
        file.write("; A.5) RL Vars\n")
        self.declare_var_helper(self.RL_var_dict, file)
        file.write("; A.6) CL Vars\n")
        self.declare_var_helper(self.CL_var_dict, file)
        file.write("; A.7) Time Vars\n")
        self.declare_var_helper(self.time_var_dict, file)
        file.write("; A.8) Entropy Vars\n")
        self.declare_var_helper(self.entropy_var_dict, file)
        file.write("; A.9) Objective Vars\n")
        self.declare_var_helper(self.obj_var_dict, file)

    def init_var(self, file):
        # initialize all the variables
        file.write("; ====== B. Initialize Variables ======\n")
        # file.write("; B.1) Initialize Q-Bit Vars\n")
        # self.assert_var_helper(self.qbit_act_var_dict, file, init_t=True)

        file.write("; B.2) Initialize Q-Bit Map Matrix Vars\n")
        self.assert_var_helper(self.qbit_map_m_var_dict, file, init_t=True)

        file.write("; B.3) Initialize Matrix Vars\n")
        self.assert_var_helper(self.m_var_dict, file, init_t=True)

        file.write("; B.4) Initialize QL Vars\n")
        self.assert_var_helper(self.QL_var_dict, file, init_t=True)

        file.write("; B.5) Initialize RL Vars\n")
        self.assert_var_helper(self.RL_var_dict, file, init_t=True)

        file.write("; B.6) Initialize CL Vars\n")
        self.assert_var_helper(self.CL_var_dict, file, init_t=True)

        file.write("; B.7) Initialize Time Vars\n")
        self.assert_var_helper(self.time_var_dict, file, init_t=True)

    def assert_matrix_const(self, file):
        # declare matrix operation
        file.write("; ====== C. Declare Matrix Constraint ======\n")
        file.write(
            "; C.1) Matrix variable can only be true if one and only one qbit is ON\n"
        )

        # if m value is true, one and only one qbit is ON
        def matrix_true_op(t):
            global constraint_idx
            for i in range(self.n_dim_):
                for j in range(self.n_dim_):
                    file.write(
                        "(assert (! (ite (= m_r{}_c{}_t{} true) \n".format(i, j, t)
                    )
                    file.write("            (and ((_ at-most 1) ")

                    for nqb in range(self.num_qbits_):
                        file.write("qbit_{}_ON_m_r{}_c{}_t{} ".format(nqb, i, j, t))
                    file.write(")\n             ((_ at-least 1) ")
                    for nqb in range(self.num_qbits_):
                        file.write("qbit_{}_ON_m_r{}_c{}_t{} ".format(nqb, i, j, t))
                    file.write(")\n             )\n")
                    # else nothing is ON
                    file.write("            (and ")
                    for nqb in range(self.num_qbits_):
                        file.write(
                            "(not qbit_{}_ON_m_r{}_c{}_t{} ) ".format(nqb, i, j, t)
                        )
                    file.write(")\n        )\n")
                    file.write(":named c{}))\n".format(constraint_idx))
                    constraint_idx += 1

        self.loop_timestamp_helper(matrix_true_op)

        file.write(
            "; C.2) Qbit mapping is true if and only if the corresponding matrix entry is true\n"
        )

        # if qbit is ON, then the corresponding matrix entry is ON
        def qbit_map_true_op(t):
            global constraint_idx
            for r in range(self.n_dim_):
                for c in range(self.n_dim_):
                    for nqb in range(self.num_qbits_):
                        file.write(
                            "(assert (! (ite (= qbit_{}_ON_m_r{}_c{}_t{} true) (= m_r{}_c{}_t{} true) (= true true)) :named c{}))\n".format(
                                nqb, r, c, t, r, c, t, constraint_idx
                            )
                        )
                        constraint_idx += 1

        self.loop_timestamp_helper(qbit_map_true_op)

        file.write("; C.3) A qbit mapping cannot be duplicated at a given time t\n")

        # at a given time t, only one qbit can be mapped to a given entry
        def qbit_map_op(t):
            global constraint_idx
            for nqb in range(self.num_qbits_):
                file.write("(assert (! ((_ at-most 1) ")
                for r in range(self.n_dim_):
                    for c in range(self.n_dim_):
                        file.write("qbit_{}_ON_m_r{}_c{}_t{} ".format(nqb, r, c, t))
                file.write(") :named c{}))\n".format(constraint_idx))
                constraint_idx += 1

        self.loop_timestamp_helper(qbit_map_op)

        file.write("; C.4) Each qbit must be mapped to an entry at a given time t\n")

        # at a given time t, each qbit must be mapped to an entry
        def qbit_map_op(t):
            global constraint_idx
            for nqb in range(self.num_qbits_):
                file.write("(assert (! ((_ at-least 1) ")
                for r in range(self.n_dim_):
                    for c in range(self.n_dim_):
                        file.write("qbit_{}_ON_m_r{}_c{}_t{} ".format(nqb, r, c, t))
                file.write(") :named c{}))\n".format(constraint_idx))
                constraint_idx += 1

        self.loop_timestamp_helper(qbit_map_op)

        file.write(
            "; C.5) Qbit mapping can be changed only if an corresponding qbit action is true\n"
        )

        # if qbit mapping is true, then the corresponding qbit action must be true
        def qbit_act_op(t):
            global constraint_idx
            for r in range(self.n_dim_):
                for c in range(self.n_dim_):
                    for nqb in range(self.num_qbits_):
                        # left operation (check if the qbit is on the left edge)
                        if c == 0:
                            pass
                        else:
                            file.write(
                                "(assert (! (ite (and (= qbit_{}_ON_m_r{}_c{}_t{} true) (= qbit_{}_L_t{} true)) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= true true)) :named c{}))\n".format(
                                    nqb,
                                    r,
                                    c,
                                    t,
                                    nqb,
                                    t,
                                    nqb,
                                    r,
                                    c - 1,
                                    t + 1,
                                    constraint_idx,
                                )
                            )
                            constraint_idx += 1
                        # right operation (check if the qbit is on the right edge)
                        if c == self.n_dim_ - 1:
                            pass
                        else:
                            file.write(
                                "(assert (! (ite (and (= qbit_{}_ON_m_r{}_c{}_t{} true) (= qbit_{}_R_t{} true)) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= true true)) :named c{}))\n".format(
                                    nqb,
                                    r,
                                    c,
                                    t,
                                    nqb,
                                    t,
                                    nqb,
                                    r,
                                    c + 1,
                                    t + 1,
                                    constraint_idx,
                                )
                            )
                            constraint_idx += 1
                        # back operation (check if the qbit is on the top edge)
                        if r == 0:
                            pass
                        else:
                            file.write(
                                "(assert (! (ite (and (= qbit_{}_ON_m_r{}_c{}_t{} true) (= qbit_{}_B_t{} true)) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= true true)) :named c{}))\n".format(
                                    nqb,
                                    r,
                                    c,
                                    t,
                                    nqb,
                                    t,
                                    nqb,
                                    r - 1,
                                    c,
                                    t + 1,
                                    constraint_idx,
                                )
                            )
                            constraint_idx += 1
                        # front operation (check if the qbit is on the bottom edge)
                        if r == self.n_dim_ - 1:
                            pass
                        else:
                            file.write(
                                "(assert (! (ite (and (= qbit_{}_ON_m_r{}_c{}_t{} true) (= qbit_{}_F_t{} true)) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= true true)) :named c{}))\n".format(
                                    nqb,
                                    r,
                                    c,
                                    t,
                                    nqb,
                                    t,
                                    nqb,
                                    r + 1,
                                    c,
                                    t + 1,
                                    constraint_idx,
                                )
                            )
                            constraint_idx += 1
                        # diag up operation
                        if r == 0 or c == self.n_dim_ - 1:
                            pass
                        else:
                            file.write(
                                "(assert (! (ite (and (= qbit_{}_ON_m_r{}_c{}_t{} true) (= qbit_{}_DU_t{} true)) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= true true)) :named c{}))\n".format(
                                    nqb,
                                    r,
                                    c,
                                    t,
                                    nqb,
                                    t,
                                    nqb,
                                    r - 1,
                                    c + 1,
                                    t + 1,
                                    constraint_idx,
                                )
                            )
                            constraint_idx += 1
                        # diag down operation
                        if r == self.n_dim_ - 1 or c == 0:
                            pass
                        else:
                            file.write(
                                "(assert (! (ite (and (= qbit_{}_ON_m_r{}_c{}_t{} true) (= qbit_{}_DD_t{} true)) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= true true)) :named c{}))\n".format(
                                    nqb,
                                    r,
                                    c,
                                    t,
                                    nqb,
                                    t,
                                    nqb,
                                    r + 1,
                                    c - 1,
                                    t + 1,
                                    constraint_idx,
                                )
                            )
                            constraint_idx += 1

        self.loop_timestamp_helper(qbit_act_op, before_last=True)

        # REUCTION FLAG : (= qbit_0_ON_m_r0_c0_t0 true) needs to be reduced since we already have the initial state
        # otherwise it enforce the next state to be the same as the initial state which is not what we want
        file.write(
            "; C.6) If no action is taken, then the qbit mapping remains the same\n"
        )

        # if entropy is false, then the qbit mapping remains the same
        def qbit_no_act_op(t):
            global constraint_idx
            for r in range(self.n_dim_):
                for c in range(self.n_dim_):
                    for nqb in range(self.num_qbits_):
                        file.write(
                            "(assert (! (ite (and (= qbit_{}_ON_m_r{}_c{}_t{} true) (= ENTROPY_qbit_{}_t{} false)) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= true true)) :named c{}))\n".format(
                                nqb, r, c, t, nqb, t, nqb, r, c, t + 1, constraint_idx
                            )
                        )
                        constraint_idx += 1

        self.loop_timestamp_helper(qbit_no_act_op, before_last=True)

        file.write("; C.7) If qbit mapping remains the same, then no action is taken\n")

        # if qbit mapping is the same in two consecutive time stamps, entropy at current time stamp is false
        def qbit_no_act_rev_op(t):
            global constraint_idx
            for r in range(self.n_dim_):
                for c in range(self.n_dim_):
                    for nqb in range(self.num_qbits_):
                        file.write(
                            "(assert (! (ite (and (= qbit_{}_ON_m_r{}_c{}_t{} true) (= qbit_{}_ON_m_r{}_c{}_t{} true)) (= ENTROPY_qbit_{}_t{} false) (= ENTROPY_qbit_{}_t{} true)) :named c{}))\n".format(
                                nqb,
                                r,
                                c,
                                t,
                                nqb,
                                r,
                                c,
                                t + 1,
                                nqb,
                                t,
                                nqb,
                                t,
                                constraint_idx,
                            )
                        )
                        constraint_idx += 1

        self.loop_timestamp_helper(qbit_no_act_rev_op, before_last=True)

        file.write("; C.8) Disable out of bound qbit action\n")

        # if qbit is on the left edge, then left action and diag down action is false
        def qbit_left_oob_op(t):
            global constraint_idx
            for r in range(self.n_dim_):
                for nqb in range(self.num_qbits_):
                    file.write(
                        "(assert (! (ite (= qbit_{}_ON_m_r{}_c{}_t{} true) (and (= qbit_{}_L_t{} false) (= qbit_{}_DD_t{} false)) (= true true)) :named c{}))\n".format(
                            nqb, r, 0, t, nqb, t, nqb, t, constraint_idx
                        )
                    )
                    constraint_idx += 1

        self.loop_timestamp_helper(qbit_left_oob_op)

        # if qbit is on the right edge, then right action and diag up action is false
        def qbit_right_oob_op(t):
            global constraint_idx
            for r in range(self.n_dim_):
                for nqb in range(self.num_qbits_):
                    file.write(
                        "(assert (! (ite (= qbit_{}_ON_m_r{}_c{}_t{} true) (and (= qbit_{}_R_t{} false) (= qbit_{}_DU_t{} false)) (= true true)) :named c{}))\n".format(
                            nqb, r, self.n_dim_ - 1, t, nqb, t, nqb, t, constraint_idx
                        )
                    )
                    constraint_idx += 1

        self.loop_timestamp_helper(qbit_right_oob_op)

        # if qbit is on the top edge, then back action and diag up action is false
        def qbit_back_oob_op(t):
            global constraint_idx
            for c in range(self.n_dim_):
                for nqb in range(self.num_qbits_):
                    file.write(
                        "(assert (! (ite (= qbit_{}_ON_m_r{}_c{}_t{} true) (and (= qbit_{}_B_t{} false) (= qbit_{}_DU_t{} false)) (= true true)) :named c{}))\n".format(
                            nqb, 0, c, t, nqb, t, nqb, t, constraint_idx
                        )
                    )
                    constraint_idx += 1

        self.loop_timestamp_helper(qbit_back_oob_op)

        # if qbit is on the bottom edge, then front action and diag down action is false
        def qbit_front_oob_op(t):
            global constraint_idx
            for c in range(self.n_dim_):
                for nqb in range(self.num_qbits_):
                    file.write(
                        "(assert (! (ite (= qbit_{}_ON_m_r{}_c{}_t{} true) (and (= qbit_{}_F_t{} false) (= qbit_{}_DD_t{} false)) (= true true)) :named c{}))\n".format(
                            nqb, self.n_dim_ - 1, c, t, nqb, t, nqb, t, constraint_idx
                        )
                    )
                    constraint_idx += 1

        self.loop_timestamp_helper(qbit_front_oob_op)

        file.write("; C.9) Qbit Localization: all movement should be localized\n")
        # if qbit is on, at least one of the surrounding entries is on in the next time stamp

        def qbit_localization_op(t):
            global constraint_idx
            for r in range(self.n_dim_):
                for c in range(self.n_dim_):
                    for nqb in range(self.num_qbits_):
                        file.write(
                            "(assert (! (ite (= qbit_{}_ON_m_r{}_c{}_t{} true) (or \n".format(
                                nqb, r, c, t
                            )
                        )
                        # current or left or right or back or front or diag up or diag down is on in the next time stamp
                        # current
                        file.write(
                            "            qbit_{}_ON_m_r{}_c{}_t{} \n".format(
                                nqb, r, c, t + 1
                            )
                        )

                        # left
                        if c != 0:
                            file.write(
                                "            qbit_{}_ON_m_r{}_c{}_t{} \n".format(
                                    nqb, r, c - 1, t + 1
                                )
                            )

                        # right
                        if c != self.n_dim_ - 1:
                            file.write(
                                "            qbit_{}_ON_m_r{}_c{}_t{} \n".format(
                                    nqb, r, c + 1, t + 1
                                )
                            )

                        # back
                        if r != 0:
                            file.write(
                                "            qbit_{}_ON_m_r{}_c{}_t{} \n".format(
                                    nqb, r - 1, c, t + 1
                                )
                            )

                        # front
                        if r != self.n_dim_ - 1:
                            file.write(
                                "            qbit_{}_ON_m_r{}_c{}_t{} \n".format(
                                    nqb, r + 1, c, t + 1
                                )
                            )

                        # diag up
                        if r != 0 and c != self.n_dim_ - 1:
                            file.write(
                                "            qbit_{}_ON_m_r{}_c{}_t{} \n".format(
                                    nqb, r - 1, c + 1, t + 1
                                )
                            )

                        # diag down
                        if r != self.n_dim_ - 1 and c != 0:
                            file.write(
                                "            qbit_{}_ON_m_r{}_c{}_t{} \n".format(
                                    nqb, r + 1, c - 1, t + 1
                                )
                            )

                        file.write(
                            "            ) (= true true)) :named c{}))\n".format(
                                constraint_idx
                            )
                        )
                        constraint_idx += 1

        self.loop_timestamp_helper(qbit_localization_op, before_last=True)

    def assert_time_abstract(self, file):
        # declare time abstract
        file.write("; ====== D. Declare Time Abstract ======\n")
        file.write(
            "; D.1) Time is not if at least one qbit action is true, then time t is true\n"
        )

        # if at least one qbit action is true, then time t is true
        def time_abs(t):
            global constraint_idx
            file.write("(assert (! (ite (or \n")
            for nqb in range(self.num_qbits_):
                file.write("               ENTROPY_qbit_{}_t{} \n".format(nqb, t))
            file.write(
                "            ) (= TIMESTAMP_t{} true) (= TIMESTAMP_t{} false)) :named c{}))\n".format(
                    t, t, constraint_idx
                )
            )
            constraint_idx += 1

        self.loop_timestamp_helper(time_abs, skip_first=True)

        file.write(
            "; D.2) Time is a series: if time t is false, then time t+1 has the same value for qbit map\n"
        )

        # if time t is false, then time t+1 has the same value for all variables
        def time_series(t):
            global constraint_idx
            file.write("(assert (! (ite (= TIMESTAMP_t{} false)\n".format(t))
            file.write("        (and\n")
            for r in range(self.n_dim_):
                for c in range(self.n_dim_):
                    for nqb in range(self.num_qbits_):
                        file.write(
                            "            (= qbit_{}_ON_m_r{}_c{}_t{} qbit_{}_ON_m_r{}_c{}_t{})\n".format(
                                nqb, r, c, t + 1, nqb, r, c, t
                            )
                        )
                    file.write(
                        "            (= m_r{}_c{}_t{} m_r{}_c{}_t{})\n".format(
                            r, c, t + 1, r, c, t
                        )
                    )
            file.write("        )\n")
            file.write("        (and true true)) :named c{}))\n".format(constraint_idx))
            constraint_idx += 1

        self.loop_timestamp_helper(time_series, before_last=True)

        file.write("; D.3) Time stamp is continous\n")

        # if time t+1 is true, then time t  is true
        def time_cont(t):
            global constraint_idx
            file.write(
                "(assert (! (ite (= TIMESTAMP_t{} true) (= TIMESTAMP_t{} true) true) :named c{}))\n".format(
                    t + 1, t, constraint_idx
                )
            )
            constraint_idx += 1

        self.loop_timestamp_helper(time_cont, before_last=True)

    def assert_entropy_abstract(self, file):
        # declare entropy abstract
        file.write("; ====== E. Declare Entropy Abstract ======\n")
        file.write("; E.1) Entropy is true if one of the qbit is moved\n")

        # if one of the qbit is moved, then entropy is true
        def entropy_abs(t):
            global constraint_idx
            for nqb in range(self.num_qbits_):
                file.write("(assert (! (ite (or \n")
                file.write(
                    "               qbit_{}_L_t{} qbit_{}_R_t{} qbit_{}_B_t{} qbit_{}_F_t{} qbit_{}_DU_t{} qbit_{}_DD_t{} \n".format(
                        nqb, t, nqb, t, nqb, t, nqb, t, nqb, t, nqb, t
                    )
                )
                file.write(
                    "            ) (= ENTROPY_qbit_{}_t{} true) (= ENTROPY_qbit_{}_t{} false)) :named c{}))\n".format(
                        nqb, t, nqb, t, constraint_idx
                    )
                )
                constraint_idx += 1

        self.loop_timestamp_helper(entropy_abs)

    def assert_swap_op(self, file):
        # declare swap operation
        file.write("; ====== F. Declare Swap Operation ======\n")

        file.write("; F.1) RL Operation\n")

        # RL barrier is lowered, then compare adjacent diagonal control rod to swap
        def swap_RL_op(t):
            global constraint_idx
            for i_rl in range(self.n_rl_rod):
                """
                if rl i (for row i) is lowered, iterate through entries at row i, for each entry (i, j)
                    if entry (i, j) has qbit ON, and ql (i + j) is smaller than ql (i + j + 1)
                        then swap qbit (i, j) and qbit (i + 1, j)
                            turn off qbit (i, j)
                            turn on qbit (i + 1, j)
                            turn off m (i, j)
                            turn on m (i + 1, j)
                            turn off qbit_map (i, j)
                            turn on qbit_map (i + 1, j)
                """
                file.write("(assert (ite (= RL_{}_t{} false) \n".format(i_rl, t + 1))
                file.write("            (and\n")
                for c in range(self.n_dim_ - 1):
                    ql_index = i_rl + c
                    # down
                    file.write(
                        "               (ite (and (< QL_{}_t{} QL_{}_t{}) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= m_r{}_c{}_t{} false))\n".format(
                            ql_index,
                            t,
                            ql_index + 1,
                            t,
                            c,
                            i_rl,
                            c,
                            t,
                            i_rl + 1,
                            c,
                            t,
                        )
                    )
                    file.write(
                        "                   (and (= qbit_{}_ON_m_r{}_c{}_t{} false) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= m_r{}_c{}_t{} true) (= m_r{}_c{}_t{} false) (= qbit_{}_F_t{} true) (= qbit_{}_B_t{} true))\n".format(
                            c,
                            i_rl,
                            c,
                            t + 1,
                            c,
                            i_rl + 1,
                            c,
                            t + 1,
                            i_rl + 1,
                            c,
                            t + 1,
                            i_rl,
                            c,
                            t + 1,
                            c,
                            t + 1,
                            c,
                            t,
                        )
                    )
                    # else:
                    file.write("                    (and true true))\n")

                file.write("            )\n")
                file.write("            (and true true)\n")
                file.write("        )\n")
                file.write(")\n")

        self.loop_timestamp_helper(swap_RL_op, before_last=True)

        # CL barrier is lowered, then compare adjacent horizontal control rod to swap
        def swap_CL_op(t):
            for i_cl in range(self.n_cl_rod):
                """
                if cl i (for column i) is lowered, iterate through entries at column i, for each entry (j, i)
                    if entry (j, i) has qbit ON, and ql (j - i) is smaller than ql (j - i + 1)
                        then swap qbit (j, i) and qbit (j, i + 1)
                            turn off qbit (j, i)
                            turn on qbit (j, i + 1)
                            turn off m (j, i)
                            turn on m (j, i + 1)
                            turn off qbit_map (j, i)
                            turn on qbit_map (j, i + 1)
                """
                file.write("(assert (ite (= CL_{}_t{} false) \n".format(i_cl, t + 1))
                file.write("            (and\n")
                for r in range(self.n_dim_ - 1):
                    ql_index = r - i_cl
                    # right
                    file.write(
                        "               (ite (and (< QL_{}_t{} QL_{}_t{}) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= m_r{}_c{}_t{} false))\n".format(
                            ql_index,
                            t,
                            ql_index + 1,
                            t,
                            r,
                            r - i_cl,
                            i_cl,
                            t,
                            r,
                            i_cl + 1,
                            t,
                        )
                    )
                    file.write(
                        "                   (and (= qbit_{}_ON_m_r{}_c{}_t{} false) (= qbit_{}_ON_m_r{}_c{}_t{} true) (= m_r{}_c{}_t{} true) (= m_r{}_c{}_t{} false) (= qbit_{}_F_t{} true) (= qbit_{}_B_t{} true))\n".format(
                            r,
                            r - i_cl,
                            i_cl,
                            t + 1,
                            r,
                            r - i_cl,
                            i_cl + 1,
                            t + 1,
                            r,
                            i_cl + 1,
                            t + 1,
                            r,
                            i_cl,
                            t + 1,
                            r,
                            t,
                            r - i_cl,
                            t,
                        )
                    )
                    # else:
                    file.write(
                        "                    (and (not (= qbit_{}_F_t{} true)) (not (= qbit_{}_B_t{} true)) true true))\n".format(
                            r, t, r - i_cl, t
                        )
                    )

                file.write("            )\n")
                file.write("            (and true true)\n")
                file.write("        )\n")
                file.write(")\n")

        self.loop_timestamp_helper(swap_CL_op, before_last=True)

    def assert_shuttle_op(self, file):
        # declare shuttle operation
        file.write("; ====== Declare Shuttle Operation ======\n")
        # if RL is on, then shuttle
        pass

    def assert_final_obj(self, file):
        global constraint_idx
        # declare final objective
        file.write("; ====== Declare Final Objective ======\n")
        """
        In this example, we want the bottom qb to be in the upper right corner within 4 steps
        """
        # at most one qbit ON at step 4 or 5
        file.write(
            "(assert (! (= qbit_0_ON_m_r0_c0_t1 true) :named c{}))\n".format(
                constraint_idx
            )
        )
        constraint_idx += 1

        # file.write(
        #     "(assert (! (= qbit_0_L_t0 true) :named c{}))\n".format(constraint_idx)
        # )
        # constraint_idx += 1

    def assert_obj_func(self, file):
        global constraint_idx
        # declare objective function
        file.write("; ====== Declare Objective Function ======\n")
        # TOTAL_TIME_TAKEN is the sum of all time variables
        file.write("(assert (! (= TOTAL_TIME_TAKEN (+ \n")
        for t in range(1, self.n_act):
            file.write("        (ite (= TIMESTAMP_t{} true) 1 0) \n".format(t))
        file.write(")) :named c{}))\n".format(constraint_idx))
        constraint_idx += 1

        # minimize the time taken
        file.write("(minimize TOTAL_TIME_TAKEN)\n")

    def conclude(self, file):
        # conclude
        file.write("; ====== Conclude ======\n")
        file.write("(check-sat)\n")
        file.write("(get-unsat-core)\n")
        file.write("(get-model)\n")
        file.write("(get-objectives)\n")

        # metrics : how many variables, literals, clauses, etc.
        file.write("; ====== Metrics ======\n")
        file.write(
            ";(Number of variables: {})\n".format(
                len(self.qbit_act_var_dict)
                + len(self.qbit_map_m_var_dict)
                + len(self.m_var_dict)
                + len(self.QL_var_dict)
                + len(self.RL_var_dict)
                + len(self.CL_var_dict)
            )
        )

    def read_res(self, lines):
        # print the result
        # each line is either (define-fun x () Bool
        # or false) and ture)
        # get the x and assign it to the corresponding variable
        prev_var = ""
        prev_res = ""
        flag_assign = False
        for line in lines:
            line = line.split()
            if line[0] == "(define-fun":
                prev_var = line[1]
            elif line[0] == "true)":
                prev_res = True
                flag_assign = True
            elif line[0] == "false)":
                prev_res = False
                flag_assign = True
            else:
                continue

            if flag_assign:
                # print("assigning {} to {}".format(prev_res, prev_var))
                if prev_var in self.qbit_act_var_dict:
                    self.qbit_act_var_dict[prev_var] = prev_res
                elif prev_var in self.qbit_map_m_var_dict:
                    self.qbit_map_m_var_dict[prev_var] = prev_res
                elif prev_var in self.m_var_dict:
                    self.m_var_dict[prev_var] = prev_res
                elif prev_var in self.QL_var_dict:
                    self.QL_var_dict[prev_var] = prev_res
                elif prev_var in self.RL_var_dict:
                    self.RL_var_dict[prev_var] = prev_res
                elif prev_var in self.CL_var_dict:
                    self.CL_var_dict[prev_var] = prev_res
                elif prev_var in self.time_var_dict:
                    self.time_var_dict[prev_var] = prev_res
                elif prev_var in self.obj_var_dict:
                    self.obj_var_dict[prev_var] = prev_res
                else:
                    # print("Error: variable {} not found".format(prev_var))
                    pass
                flag_assign = False

    def print_true_qbit(self):
        # get the true qbit
        for qbit in self.qbit_act_var_dict:
            if self.qbit_act_var_dict[qbit]:
                print(qbit)

    def print_true_qbit_map(self):
        # get the true qbit map
        for qbit_map in self.qbit_map_m_var_dict:
            if self.qbit_map_m_var_dict[qbit_map]:
                print(qbit_map + " ==> " + str(self.qbit_map_m_var_dict[qbit_map]))

    def print_true_m(self):
        # get the true m
        for m in self.m_var_dict:
            if self.m_var_dict[m]:
                print(m + " ==> " + str(self.m_var_dict[m]))

    def print_true_QL(self):
        # get the true QL
        for ql in self.QL_var_dict:
            if self.QL_var_dict[ql]:
                print(ql + " ==> " + str(self.QL_var_dict[ql]))

    def print_true_RL(self):
        # get the true RL
        for rl in self.RL_var_dict:
            if self.RL_var_dict[rl]:
                print(rl + " ==> " + str(self.RL_var_dict[rl]))

    def print_true_CL(self):
        # get the true CL
        for cl in self.CL_var_dict:
            if self.CL_var_dict[cl]:
                print(cl + " ==> " + str(self.CL_var_dict[cl]))

    def print_true_time(self):
        # get the true time
        for time in self.time_var_dict:
            if self.time_var_dict[time]:
                print(time + " ==> " + str(self.time_var_dict[time]))

    def print_true_obj(self):
        # get the true obj
        for obj in self.obj_var_dict:
            if self.obj_var_dict[obj]:
                print(obj + " ==> " + str(self.obj_var_dict[obj]))

    def get_true_var_helper(self, var_dict):
        res = []
        for var in var_dict:
            if var_dict[var]:
                res.append(var)
        return res

    def view_solution(self):
        def printTimeStamp(t):
            # at time 0, print the board
            print("################## TimeStamp {} ##################".format(t))
            print("===== Q-Bit =====")
            t0_qbit_act_var_dict = self.get_by_timestamp_helper(
                self.qbit_act_var_dict, t
            )
            for qbit in t0_qbit_act_var_dict:
                if t0_qbit_act_var_dict[qbit]:
                    print(qbit)
            t0_qbit_map_m_var_dict = self.get_by_timestamp_helper(
                self.qbit_map_m_var_dict, t
            )
            # map the qbit to the board
            for qbit_map in t0_qbit_map_m_var_dict:
                if t0_qbit_map_m_var_dict[qbit_map]:
                    print(qbit_map + " ==> " + str(t0_qbit_map_m_var_dict[qbit_map]))
            print("===== Board =====")
            self.print_lattice(qbit_map_m_var_dict_=t0_qbit_map_m_var_dict)

        self.loop_timestamp_helper(printTimeStamp)

        print("################## Objective ##################")
        self.print_true_time()
        self.print_true_obj()
