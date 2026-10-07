''' Downloads recent benchmarks from the Global Benchmark Database (GBD, https://benchmark-database.de)

    Instances of the main tracks of the SAT competitions 2020-2025, small enough for a Python solver.
    Selected with the GBD query (2026-10-07):
        track like %main_202% and minisat1m = yes and clauses < 40000
    (minisat1m: solved by minisat in less than one minute; this does not mean they are easy for pysat)

    Each instance is given by its GBD hash (its unique identifier, independent of the file name).
    The files are saved in examples/recent/ as <hash>-<name> (as GBD names them).

    Usage: python fetch_gbd.py [family ...]     (no argument: all the instances)
'''

import os, sys, urllib.request

GBD = 'https://benchmark-database.de/file/'
DEST = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'recent')

# (GBD hash, file name, family, result, variables, clauses, main tracks)
INSTANCES = [
    ('b9f858634fabf35872d7e5df7938d995', 'Circuit_multiplier33.cnf.xz', 'circuit-multiplier', 'sat', 1119, 21861, 'main_2021'),
    ('037c423f56548082b1935e88c48ffdda', '3col120_5_2.shuffled.cnf.xz', 'coloring', 'sat', 240, 1026, 'main_2023'),
    ('571a2f223784fb92a53b4cc8cc8b569e', 'clqcolor-08-06-07.shuffled-as.sat05-1257.cnf.xz', 'coloring', 'unsat', 132, 1527, 'main_2023'),
    ('28f29fe949422ec88892e18073de065c', '5col100_15_6.shuffled.cnf.xz', 'coloring', 'unsat', 300, 4059, 'main_2023'),
    ('0928111a3d5d5ce05dffb83cb5982eba', 'Steiner-9-5-bce.cnf.xz', 'cover', 'unsat', 54, 58, 'main_2020'),
    ('5a5fb82a3672ee898465aa8f1103147f', 'Steiner-15-7-bce.cnf.xz', 'cover', 'unsat', 150, 153, 'main_2020'),
    ('a5507d7a8dacbc0ecd7abc8d631c266a', 'Steiner-27-10-bce.cnf.xz', 'cover', 'unsat', 513, 460, 'main_2020'),
    ('dac6f7f51d4aad660422a31ed0ee2456', 'Steiner-45-16-bce.cnf.xz', 'cover', 'unsat', 1395, 1261, 'main_2020'),
    ('911cbc796d15eb316d36c82c90fd7d11', 'c499_gr_2pin_w6.shuffled.cnf.xz', 'fpga-routing', 'sat', 2070, 22470, 'main_2023'),
    ('24b93d0bf941e4b050c9109e4cb7faf4', 'connm-ue-csp-sat-n600-d-0.02-s1022905465.used-as.sat04-951.cnf.xz', 'generic-csp', 'sat', 556, 6427, 'main_2023'),
    ('6e139783cfbcfeec85b49750ad11a615', 'x9-06068.sat.sanitized.cnf.xz', 'hamiltonian', 'sat', 300, 2696, 'main_2025'),
    ('a497d784c61c330f012dcd80d44dcd43', 'x9-06099.sat.sanitized.cnf.xz', 'hamiltonian', 'sat', 300, 2698, 'main_2025'),
    ('695d8f6a2ee6e89e5a4f5d94abc3aca6', 'x9-07092.sat.sanitized.cnf.xz', 'hamiltonian', 'sat', 350, 3147, 'main_2025'),
    ('b2c92aebc75da8a15a5388b559b85623', 'sp4-33-una-stri-flat-noid.cnf.xz', 'minimal-superpermutation', 'unsat', 819, 4423, 'main_2021'),
    ('5ea9d54e4eb8eeab1ff058471b9c83ca', 'sp4-33-one-nons-flat-noid.cnf.xz', 'minimal-superpermutation', 'sat', 852, 11560, 'main_2021'),
    ('00f2eb377986e7decbc863931680a3b2', 'rand_net70-40-10.shuffled.cnf.xz', 'miter', 'unsat', 5600, 16661, 'main_2023'),
    ('1aa7cd96ab1f7bf58984deccf8362ab4', 'rand_net50-60-10.shuffled.cnf.xz', 'miter', 'unsat', 6000, 17901, 'main_2023'),
    ('362d153b4162127bc42796180110f483', 'Carry_Bits_Fast_19.cnf.cnf.xz', 'multiplier-circuits', 'sat', 5892, 23367, 'main_2025'),
    ('5ac44f542fd2cd4492067deb7791629a', 'Carry_Bits_Fast_18.cnf.cnf.xz', 'multiplier-circuits', 'sat', 5892, 23367, 'main_2022'),
    ('d87714e099c66f0034fb95727fa47ccc', 'Wallace_Bits_Fast_2.cnf.cnf.xz', 'multiplier-circuits', 'sat', 5892, 23367, 'main_2022'),
    ('17039a3ed02ea12653ec5389e56dab50', 'pbl-00070.shuffled-as.sat05-1324.shuffled-as.sat05-1324.cnf.xz', 'pebbling', 'unsat', 257, 7375, 'main_2023'),
    ('44092fcc83a5cba81419e82cfd18602c', 'php-010-009.shuffled-as.sat05-1185.cnf.xz', 'pigeon-hole', 'unsat', 90, 415, 'main_2023'),
    ('36c342091848d5d6a1a8eeb3a8b49b86', 'rovers1_ks99i.renamed-as.sat05-3971.cnf.xz', 'planning', 'sat', 439, 5423, 'main_2023'),
    ('578f9377bfbfcc6ea3a18eb630667956', 'ferry8_ks99i.renamed-as.sat05-4005.cnf.xz', 'planning', 'sat', 2547, 32525, 'main_2023'),
    ('a9c0f64594a3eaede246b31eb3bc839b', 'mp1-Nb6T06.cnf.xz', 'polynomial-multiplication', 'unsat', 3702, 15840, 'main_2017,main_2021'),
    ('24bf910d2b9da558fb3e71a4dbe79ba3', 'lisa19_99_a.shuffled.cnf.xz', 'prime-factoring', 'sat', 1201, 6563, 'main_2023'),
    ('028d0cc7af63e9bba5795f20e24db4f6', 'pyhala-braun-sat-35-4-04.shuffled.cnf.xz', 'prime-factoring', 'sat', 7383, 24320, 'main_2023'),
    ('aa09403249f021450cc798cc560a14a3', 'prime_a20_b20.cnf.xz', 'prime-testing', 'sat', 6360, 32019, 'main_2021'),
    ('fe19a31b76cbba5901e16ce36c7578ed', 'C208_FA_UT_3254.cnf.xz', 'product-configuration', 'unsat', 1805, 7334, 'main_2023'),
    ('70af2c3bfd44bcf9baa2a9605f4a17fe', 'gensys-icl002.shuffled-as.sat05-2714.cnf.xz', 'quasigroup-completion', 'unsat', 1444, 7479, 'main_2023'),
    ('211938776d92f11870a687abd11d55a4', 'iso-icl004.shuffled-as.sat05-3238.cnf.xz', 'quasigroup-completion', 'unsat', 1000, 9897, 'main_2023'),
    ('71bca76153c6ee65b72a517fd658a42d', 'iso-brn100.shuffled-as.sat05-3025.cnf.xz', 'quasigroup-completion', 'sat', 3587, 10984, 'main_2023'),
    ('587150fb7b12a6b5dd7e4a9446b9713b', 'iso-ukn004.shuffled-as.sat05-3385.cnf.xz', 'quasigroup-completion', 'sat', 1889, 12666, 'main_2023'),
    ('d1a62a8688c6c4fabd0dec3770ce40dd', 'qwh.40.560.shuffled-as.sat03-1654.cnf.xz', 'quasigroup-completion', 'sat', 3100, 26345, 'main_2023'),
    ('09d7add3bf3b75c5d1023a92e752989a', 'Break_unsat_04_03.xml.cnf.xz', 'scheduling', 'unsat', 221, 1085, 'main_2024'),
    ('69f6dd335626a9b71bfc6f2332f52b9d', 'Break_04_04.xml.cnf.xz', 'scheduling', 'sat', 227, 1106, 'main_2025'),
    ('081f111af59344b61346367a930e24f6', 'Break_triple_04_06.xml.cnf.xz', 'scheduling', 'sat', 252, 1163, 'main_2025'),
    ('7f7109dce621ef361a72b3e8cee9a962', 'Break_unsat_06_07.xml.cnf.xz', 'scheduling', 'unsat', 1101, 5037, 'main_2024'),
    ('c801a020a6c8bc3c287fea495203b114', 'worker_20_40_20_0.95.cnf.xz', 'scheduling', 'sat', 656, 11934, 'main_2024'),
    ('3988a60c6e93167763c6fd2a347d5859', 'Break_08_24.xml.cnf.xz', 'scheduling', 'sat', 3890, 14188, 'main_2024'),
    ('965bc4f6691b2e5f7388aaa9ba68f768', 'SCPC-500-5.cnf.xz', 'set-covering', 'unsat', 500, 15530, 'main_2025'),
    ('75cc1f02ed4b8c06553ef579b163e1be', 'SCPC-500-14.cnf.xz', 'set-covering', 'unsat', 500, 15585, 'main_2025'),
    ('663bb5659e42c2c75f74354f48895302', 'SCPC-500-13.cnf.xz', 'set-covering', 'unsat', 500, 15618, 'main_2025'),
    ('03de316ba1e90305471a3b8620cb9cd7', 'satsgi-n23himBHm26-p0-q248.cnf.xz', 'subgraph-isomorphism', 'sat', 598, 14076, 'main_2023'),
    ('27b4fe4cb0b4e2fd8327209ca5ff352c', 'grid_10_20.shuffled.cnf.xz', 'theorem-proving', 'unsat', 398, 741, 'main_2023'),
    ('01d142c43f3ce9a8c5ef7a1ecdbb6cba', 'urquhart3_25bis.shuffled.cnf.xz', 'tseitin-formulas', 'unsat', 99, 264, 'main_2022'),
    ('0297c2a35f116ffd5382aea5b421e6df', 'Urquhart-s3-b3.shuffled-as.sat03-1556.cnf.xz', 'tseitin-formulas', 'unsat', 45, 376, 'main_2023'),
]

def fetch(families = None):
    os.makedirs(DEST, exist_ok=True)
    for h, name, family, result, nbvars, nbclauses, track in INSTANCES:
        if families and family not in families: continue
        path = os.path.join(DEST, h + '-' + name)
        if os.path.exists(path):                                   # Already there
            continue
        print("c {f:28s} {r:5s} {v:6d} vars {c:6d} clauses  {n:s}".format(f=family, r=result, v=nbvars, c=nbclauses, n=name))
        with urllib.request.urlopen(GBD + h, timeout=60) as answer, open(path + '.part', 'wb') as out:
            out.write(answer.read())
        os.rename(path + '.part', path)                            # (no half downloaded file if interrupted)

if __name__ == "__main__":
    fetch(sys.argv[1:])
