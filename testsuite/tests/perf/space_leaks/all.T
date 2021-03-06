
test('space_leak_001',
     # Before trac #2747 was fixed this was 565.
     # Now it's: 3 (amd64/Linux)
     #           4 (x86/OS X)
     #           5 (x86/Linux)
     [stats_num_field('peak_megabytes_allocated', (3, 1)),
                        # 3 (amd64/Linux, integer-gmp2)
      stats_num_field('max_bytes_used',
          [(wordsize(64), 440000, 15),
                        # 440224 (amd64/Linux)
                        # 417016 (x86/OS X)
                        # 415672 (x86/Windows)
                        # 481456 (unreg amd64/Linux)
           (wordsize(32), 405650, 10)]),
             # 2013-02-10 372072 (x86/OSX)
             # 2013-02-10 439228 (x86/OSX)

      stats_num_field('bytes allocated', 
           [ (wordsize(64), 11315747416, 5),
                        # expected value: 9079316016 (amd64/Linux)
                        #                 9331570416 (x86/Linux)
                        #                 9329073952 (x86/OS X)
                        #                 9327959840 (x86/Windows)
                        #                 11315747416 (amd64/Lnx, integer-gmp2)

             (wordsize(32), 13550759068, 5),
            # 2014-12-01  13550759068 (Windows)
              
            ]),
      omit_ways(['profasm','profthreaded','threaded1','threaded2'])
      ],
     compile_and_run,
     [''])

test('T4334',
     # Test for a space leak in Data.List.lines (fixed with #4334)
     [extra_run_opts('1000000 2 t'),
      stats_num_field('peak_megabytes_allocated', (2, 1)),
      # prof ways don't work well with +RTS -V0
      omit_ways(['profasm','profthreaded'])
      ],
     compile_and_run, [''])

test('T2762',
     [# peak_megabytes_allocated is 2 with 7.0.2.
      # Was 57 with 6.12.3.
      stats_num_field('peak_megabytes_allocated', (2, 0)),
      only_ways(['normal']),
      extra_clean(['T2762A.hi', 'T2762A.o'])],
     compile_and_run, ['-O'])

test('T4018',
     [ only_ways(['optasm']), extra_run_opts('+RTS -M10m -RTS') ],
     compile_and_run, ['-fno-state-hack'])

test('T4029',
     [stats_num_field('peak_megabytes_allocated',
          [(wordsize(64), 66, 10)]),
            # 2016-02-26: 66 (amd64/Linux)           INITIAL
      stats_num_field('max_bytes_used',
          [(wordsize(64), 24071720, 5)])
            # 2016-02-26: 24071720 (amd64/Linux)     INITIAL
      ],
     ghci_script,
     ['T4029.script'])
