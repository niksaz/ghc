test('testblockalloc',
     [c_src, only_ways(['normal','threaded1']), extra_run_opts('+RTS -I0')],
     compile_and_run, [''])

test('testmblockalloc',
     [c_src, only_ways(['normal','threaded1']), extra_run_opts('+RTS -I0')],
     compile_and_run, [''])
# -I0 is important: the idle GC will run the memory leak detector,
# which will crash because the mblocks we allocate are not in a state
# the leak detector is expecting.


# See bug #101, test requires +RTS -c (or equivalently +RTS -M<something>)
# only GHCi triggers the bug, but we run the test all ways for completeness.
test('bug1010', normal, compile_and_run, ['+RTS -c -RTS'])
test('derefnull',
     [# LLVM Optimiser considers dereference of a null pointer
      # undefined and marks the code as unreachable which means
      # that later optimisations remove it altogether.
      omit_ways(['optllvm']),
      # SIGSEGV on Linux (which we make the default)
      exit_code(139),
      # Apparently the output can be different on different
      # Linux setups, so just ignore it. As long as we get
      # the right exit code we're OK.
      when(opsys('linux'), ignore_output),
      # SIGBUS on OX X (PPC and x86 only; amd64 gives SEGV)
      when(platform('i386-apple-darwin'), exit_code(138)),
      when(platform('powerpc-apple-darwin'), exit_code(138)),
      when(opsys('mingw32'), exit_code(1)),
      # since these test are supposed to crash the
      # profile report will be empty always.
      # so disable the check for profiling
      when(opsys('mingw32'), omit_ways(prof_ways))],
     compile_and_run, [''])
test('divbyzero',
     [# SIGFPE on Linux
      exit_code(136),
      # Apparently the output can be different on different
      # Linux setups, so just ignore it. As long as we get
      # the right exit code we're OK.
      when(opsys('linux'), ignore_output),
      # PowerPC 64 bit and most likely PowerPC 32 bit processors
      # do not generate an exception (interrupt) for integer
      # division by zero but the result is undefined.
      # C programs compiled with gcc exit normally, so do we.
      when(platform('powerpc64-unknown-linux'), exit_code(0)),
      when(platform('powerpc64le-unknown-linux'), exit_code(0)),
      when(opsys('mingw32'), exit_code(1)),
      # since these test are supposed to crash the
      # profile report will be empty always.
      # so disable the check for profiling
      when(opsys('mingw32'), omit_ways(prof_ways))],
     compile_and_run, [''])

test('outofmem', when(opsys('darwin'), skip),
                 run_command, ['$MAKE -s --no-print-directory outofmem'])
test('outofmem2', normal, run_command, ['$MAKE -s --no-print-directory outofmem2'])

test('T2047', [ignore_output, extra_run_opts('+RTS -c -RTS')],
              compile_and_run, ['-package containers'])

# Blackhole-detection test.
# Skip GHCi due to #2786
test('T2783', [ omit_ways(['ghci']), exit_code(1) ], compile_and_run, [''])

# Test the work-stealing deque implementation.  We run this test in
# both threaded1 (-threaded -debug) and threaded2 (-threaded) ways.
test('testwsdeque', [unless(in_tree_compiler(), skip),
                    req_smp, # needs atomic 'cas'
                    c_src, only_ways(['threaded1', 'threaded2'])],
                    compile_and_run, ['-I../../../rts'])

test('T3236', [c_src, only_ways(['normal','threaded1']), exit_code(1)], compile_and_run, [''])

test('stack001', extra_run_opts('+RTS -K32m -RTS'), compile_and_run, [''])
test('stack002', extra_run_opts('+RTS -K32m -k4m -RTS'), compile_and_run, [''])

# run this test with very small stack chunks to exercise the stack
# overflow/underflow machinery.
test('stack003', [ omit_ways('ghci'), # uses unboxed tuples
                   extra_run_opts('500000 +RTS -kc1k -kb100 -K96m -RTS') ],
                 compile_and_run, [''])

test('atomicinc', [ c_src, only_ways(['normal','threaded1', 'threaded2']) ], compile_and_run, [''])

test('T3424', # it's slow:
              [ when(fast(), skip), only_ways(['normal','threaded1','ghci']) ],
              compile_and_run, [''])

# Test for out-of-range heap size
test('rtsflags001', [ only_ways(['normal']), exit_code(1), extra_run_opts('+RTS -H0m -RTS') ], compile_and_run, [''])

# Crashed with 7.2 and earlier
test('rtsflags002', [ only_ways(['normal']) ], compile_and_run, ['-with-rtsopts="-B -B -B"'])

# Test to see if linker scripts link properly to real ELF files
test('T2615',
     [ when(opsys('mingw32'), skip),
       # OS X doesn't seem to support linker scripts
       when(opsys('darwin'), skip),
       # Solaris' linker does not support GNUish linker scripts
       when(opsys('solaris2'), skip),
       pre_cmd('$MAKE -s --no-print-directory T2615-prep'),
       # Add current directory to dlopen search path
       cmd_prefix('LD_LIBRARY_PATH=$LD_LIBRARY_PATH:. '),
       extra_clean(['libfoo_T2615.so', 'libfoo_T2615.o'])],
     compile_and_run,
     ['-package ghc'])

# omit dyn and profiling ways, because we don't build dyn_l or p_l
# variants of the RTS by default
test('traceEvent', [ omit_ways(['dyn'] + prof_ways),
                     extra_run_opts('+RTS -ls -RTS') ],
                   compile_and_run, ['-eventlog'])

test('T4059',
     extra_clean(['T4059_c.o']),
     run_command,
     ['$MAKE -s --no-print-directory T4059'])

# Test for #4274
test('exec_signals', [
     when(opsys('mingw32'), skip),
     pre_cmd('$MAKE -s --no-print-directory exec_signals-prep'),
     cmd_prefix('./exec_signals_prepare'),
     extra_clean(['exec_signals_child', 'exec_signals_prepare'])
    ], compile_and_run, [''])

test('return_mem_to_os', normal, compile_and_run, [''])

test('T4850', when(opsys('mingw32'), expect_broken(4850)), run_command, ['$MAKE -s --no-print-directory T4850'])

def config_T5250(name, opts):
    if not (config.arch in ['i386','x86_64']):
        opts.skip = 1;

test('T5250', [ config_T5250,
                # stack ptr is not 16-byte aligned on 32-bit Windows
                when(platform('i386-unknown-mingw32'), expect_fail),
                when(platform('i386-unknown-linux'),
                            expect_broken_for(4211,['llvm'])),
                extra_clean(['spalign.o']),
                omit_ways(['ghci']) ],
              compile_and_run, ['spalign.c'])

test('T5423',
     extra_clean(['T5423_cmm.o']),
     run_command,
     ['$MAKE -s --no-print-directory T5423'])

# Workaround bug #8458: old dlopen opens sections in the wrong order,
# so we just accept both orders.
def checkDynAsm(actual_file, normaliser):
    actual_raw = read_no_crs(actual_file)
    actual_str = normaliser(actual_raw)
    actual = actual_str.split()
    if actual == ['initArray1', 'initArray2', 'ctors1', 'ctors2', 'success']:
        return 1
    elif actual == ['ctors1', 'ctors2', 'initArray1', 'initArray2', 'success']:
        if_verbose(1, 'T5435_dyn_asm detected old-style dlopen, see #8458')
        return 1
    elif opsys('darwin') and actual == ['modInitFunc1', 'modInitFunc2', 'success']:
        return 1
    elif opsys('mingw32') and actual == ['ctors1', 'ctors2', 'success']:
        return 1
    else:
        if_verbose(1, 'T5435_dyn_asm failed with %s, see all.T for details' % actual)
        return 0

# These should have extra_clean() arguments, but I need
# to somehow extract out the name of DLLs to do that

test('T5435_v_asm', when(arch('powerpc64'), expect_broken(11259)), run_command, ['$MAKE -s --no-print-directory T5435_v_asm'])
test('T5435_v_gcc', when(arch('powerpc64'), expect_broken(11259)), run_command, ['$MAKE -s --no-print-directory T5435_v_gcc'])
test('T5435_dyn_asm', check_stdout(checkDynAsm), run_command, ['$MAKE -s --no-print-directory T5435_dyn_asm'])
test('T5435_dyn_gcc', normal , run_command, ['$MAKE -s --no-print-directory T5435_dyn_gcc'])

test('T5993', extra_run_opts('+RTS -k8 -RTS'), compile_and_run, [''])

test('T6006', [ omit_ways(prof_ways + ['ghci']),
                 extra_clean(['T6006_c.o']),
                 pre_cmd('$MAKE -s --no-print-directory T6006_setup') ],
                 # The T6006_setup hack is to ensure that we generate
                 # T6006_stub.h before compiling T6006_c.c, which
                 # needs it.
               compile_and_run, ['T6006_c.c -no-hs-main'])

test('T7037',
     [ extra_clean(['T7037_main.o','T7037_main']) ],
     run_command,
     ['$MAKE -s --no-print-directory T7037'])

test('T7087', exit_code(1), compile_and_run, [''])
test('T7160', normal, compile_and_run, [''])

test('T7040', [ extra_clean(['T7040_c.o']), omit_ways(['ghci']) ],
     compile_and_run, ['T7040_c.c'])

test('T7040_ghci', [ only_ways(['ghci']),
                      pre_cmd('$MAKE -s --no-print-directory T7040_ghci_setup'),
                      extra_clean(['T7040_ghci_c.o']) ],
                    compile_and_run, ['T7040_ghci_c.o'])

test('T7227', [ extra_run_opts('+RTS -tT7227.stat --machine-readable -RTS'),
                extra_clean(['T7227.stat']) ]
            , compile_and_run, [''] )

test('T7636', [ exit_code(1), extra_run_opts('100000') ], compile_and_run, [''] )

test('stablename001', expect_fail_for(['hpc']), compile_and_run, [''])
# hpc should fail this, because it tags every variable occurrence with
# a different tick.  It's probably a bug if it works, hence expect_fail.

test('T7815', [ multi_cpu_race,
                extra_run_opts('50000 +RTS -N2 -RTS'),
                req_smp,
                only_ways(['threaded1', 'threaded2']) ], compile_and_run, [''] )

# ignore_output because it contains a unique:
#   ffishutdown: Main_dul: interrupted
test('ffishutdown', [ ignore_output, only_ways(['threaded1','threaded2']) ], compile_and_run, [''])

test('T7919',
     [extra_clean(['T7919A.o','T7919A.hi', 'T7919A.dyn_o','T7919A.dyn_hi']),
      when(fast(), skip), omit_ways(prof_ways)],
     compile_and_run, [config.ghc_th_way_flags])

test('T8035', normal, compile_and_run, [''])

test('linker_unload',
     [ when(arch('powerpc64'), expect_broken(11259)),
       extra_clean(['Test.o','Test.hi', 'linker_unload']) ],
     run_command,
     ['$MAKE -s --no-print-directory linker_unload'])

test('T8209', [ only_ways(threaded_ways), ignore_output ],
              compile_and_run, [''])

test('T8242', [ only_ways(threaded_ways), ignore_output ],
              compile_and_run, [''])

test('T8124', [ only_ways(threaded_ways), omit_ways(['ghci']),
                 when(opsys('mingw32'), skip), # uses pthreads
                 extra_clean(['T8124_c.o']),
                 pre_cmd('$MAKE -s --no-print-directory T8124_setup') ],
                 # The T8124_setup hack is to ensure that we generate
                 # T8124_stub.h before compiling T8124_c.c, which
                 # needs it.
               compile_and_run, ['T8124_c.c -no-hs-main'])

# +RTS -A8k makes it fail faster
# The ghci way gets confused by the RTS options
test('T9045', [ omit_ways(['ghci']), extra_run_opts('10000 +RTS -A8k -RTS') ], compile_and_run, [''])

# I couldn't reproduce 9078 with the -threaded runtime, but could easily
# with the non-threaded one.
test('T9078', [ omit_ways(threaded_ways) ], compile_and_run, ['-with-rtsopts="-DS" -debug'])

test('T10017', [ when(opsys('mingw32'), skip)
               , only_ways(threaded_ways), extra_run_opts('+RTS -N2 -RTS') ], compile_and_run, [''])

test('rdynamic', [ unless(opsys('linux') or opsys('mingw32'), skip)
                 # this needs runtime infrastructure to do in ghci:
                 #  '-rdynamic' ghc, load modules only via dlopen(RTLD_BLOBAL) and more.
                 , omit_ways(['ghci'])
                 ],
     compile_and_run, ['-rdynamic -package ghc'])

test('GcStaticPointers', [when(doing_ghci(), extra_hc_opts('-fobject-code'))],
     compile_and_run, [''])
test('ListStaticPointers', [when(doing_ghci(), extra_hc_opts('-fobject-code'))],
     compile_and_run, [''])

# 251 = RTS exit code for "out of memory"
test('overflow1', [ exit_code(251) ], compile_and_run, [''])
test('overflow2', [ exit_code(251) ], compile_and_run, [''])
test('overflow3', [ exit_code(251) ], compile_and_run, [''])

test('linker_error1',
     [ extra_clean(['linker_error1.o','linker_error1']), ignore_output ],
     run_command,
     ['$MAKE -s --no-print-directory linker_error1'])

test('linker_error2',
     [ extra_clean(['linker_error2.o','linker_error2_c.o', 'linker_error2']),
       ignore_output ],
     run_command,
     ['$MAKE -s --no-print-directory linker_error2'])

test('linker_error3',
     [ extra_clean(['linker_error3.o','linker_error3_c.o', 'linker_error3']),
       ignore_output ],
     run_command,
     ['$MAKE -s --no-print-directory linker_error3'])

test('T9839_01', [ no_stdin, ignore_output],
                run_command,
                ['{compiler} -e 1 +RTS -T-s 2>&1 | \
                  grep "flag -T given an argument when none was expected: -T-s"'])

test('T9839_02', [ only_ways(prof_ways), ignore_output, exit_code(1), extra_run_opts('+RTS -Pax')],
                compile_and_run,
                [''])

test('T9839_03', [ only_ways(prof_ways), ignore_output, exit_code(1), extra_run_opts('+RTS -Px')],
                compile_and_run,
                [''])

test('T9839_04', [ only_ways(prof_ways), ignore_output, exit_code(0), extra_run_opts('+RTS -xc')],
                compile_and_run,
                [''])

test('T9839_05', [ only_ways(prof_ways), ignore_output, exit_code(1), extra_run_opts('+RTS -xcx')],
                compile_and_run,
                [''])

test('T9839_06', [ only_ways(prof_ways), ignore_output, exit_code(1), extra_run_opts('+RTS -xtx')],
                compile_and_run,
                [''])

# ignore_output as RTS reports slightly different error messages
# in 'epoll' and 'select' backends on reading from EBADF
# mingw32 skip as UNIX pipe and close(fd) is used to exercise the problem
test('T10590', [ignore_output, when(opsys('mingw32'),skip)], compile_and_run, [''])

# 20000 was easily enough to trigger the bug with 7.10
test('T10904', [ omit_ways(['ghci']), extra_run_opts('20000') ],
               compile_and_run, ['T10904lib.c'])

test('T10728', [extra_run_opts('+RTS -maxN3 -RTS'), only_ways(['threaded2'])],
               compile_and_run, [''])
