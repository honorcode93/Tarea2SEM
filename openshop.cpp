/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */
/*
 *  Main authors:
 *     Guido Tack <tack@gecode.org>
 *
 *  Copyright:
 *     Guido Tack, 2009
 *
 *  Last modified:
 *     $Date: 2015-03-17 16:09:39 +0100 (Tue, 17 Mar 2015) $ by $Author: schulte $
 *     $Revision: 14447 $
 *
 *  This file is part of Gecode, the generic constraint
 *  development environment:
 *     http://www.gecode.org
 *
 *  Permission is hereby granted, free of charge, to any person obtaining
 *  a copy of this software and associated documentation files (the
 *  "Software"), to deal in the Software without restriction, including
 *  without limitation the rights to use, copy, modify, merge, publish,
 *  distribute, sublicense, and/or sell copies of the Software, and to
 *  permit persons to whom the Software is furnished to do so, subject to
 *  the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 *  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 *  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 *  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

#include <gecode/driver.hh>
#include <gecode/int.hh>
#include <gecode/minimodel.hh>

using namespace Gecode;

namespace {
  /**
   * \brief Specification of an open shop instance
   *
   */
  class OpenShopSpec {
  public:
    const int m;  //< number of machines
    const int n;  //< number of jobs
    const int* p; //< processing times of the tasks
    /// Constructor
    OpenShopSpec(int m0, int n0, const int* p0) : m(m0), n(n0), p(p0) {}
  };

  extern OpenShopSpec examples[];
  extern const unsigned int n_examples;
}

/**
 * \brief %Example: open-shop scheduling
 *
 * \ingroup Example
 *
 */
class OpenShop : public IntMinimizeScript {
protected:
  /// The instance specification
  const OpenShopSpec& spec;
  /// Precedences
  BoolVarArray b;
  /// Makespan
  IntVar makespan;
  /// Start times
  IntVarArray _start;

  /// %Task representation for CROSH heuristic
  class Task {
  public:
    int j; //< Job
    int m; //< Machine
    int p; //< Processing time
    /// Default constructor
    Task(void) {}
    /// Constructor
    Task(int j0, int m0, int p0) : j(j0), m(m0), p(p0) {}
  };

  /** \brief Use Constructive Randomized Open-Shop Heuristics
   *         to compute lower and upper bounds
   *
   * This heuristic is taken from the paper
   * A. Malapert, H. Cambazard, C. Gueret, N. Jussien, A. Langevin,
   * L.-M. Rousseau: An Optimal Constraint Programming Approach to the
   * Open-Shop Problem. Technical report, CIRRELT-2009-25.
   *
   */
  void crosh(Matrix<IntArgs>& dur, int& minmakespan, int& maxmakespan) {
    Support::RandomGenerator rnd;

    // Compute maximum makespan as the sum of all production times.
    maxmakespan = 0;
    for (int i=0; i<spec.m; i++)
      for (int j=0; j<spec.n; j++)
        maxmakespan += dur(i,j);

    // Compute minimum makespan as the maximum of individual jobs and machines
    minmakespan = 0;
    for (int i=0; i<spec.m; i++) {
      int ms = 0;
      for (int j=0; j<spec.n; j++) {
        ms += dur(i,j);
      }
      minmakespan = std::max(minmakespan, ms);
    }
    for (int j=0; j<spec.n; j++) {
      int ms = 0;
      for (int i=0; i<spec.m; i++) {
        ms += dur(i,j);
      }
      minmakespan = std::max(minmakespan, ms);
    }

    Region re(*this);
    int* ct_j = re.alloc<int>(spec.n); // Job completion time
    int* ct_m = re.alloc<int>(spec.m); // Machine completion time
    Task* tasks = re.alloc<Task>(spec.n*spec.m); // Tasks
    int k=0;
    for (int i=spec.m; i--;)
      for (int j=spec.n; j--;)
        new (&tasks[k++]) Task(j,i,dur(i,j));
    int* t0_tasks = re.alloc<int>(spec.n*spec.m); // Earliest possible tasks
    
    bool stopCROSH = false;

    int maxIterations;
    switch (spec.n) {
    case 3: maxIterations = 5; break;
    case 4: maxIterations = 25; break;
    case 5: maxIterations = 50; break;
    case 6: maxIterations = 1000; break;
    case 7: maxIterations = 10000; break;
    case 8: maxIterations = 10000; break;
    case 9: maxIterations = 10000; break;
    default: maxIterations = 25000; break;
    }
    int iteration = 0;
    while (!stopCROSH && maxmakespan > minmakespan) {
      for (int i=spec.n; i--;) ct_j[i] = 0;
      for (int i=spec.m; i--;) ct_m[i] = 0;
      int cmax = 0; // Current makespan
      int u = spec.n*spec.m; // Consider all tasks
      while (u > 0) {
        int u_t0 = 0; // Set of selectable tasks
        int t0 = maxmakespan; // Minimal head of unscheduled tasks
        for (int i=0; i<u; i++) {
          const Task& t = tasks[i];
          int est = std::max(ct_j[t.j], ct_m[t.m]); // Head of T_jm
          if (est < t0) {
            t0 = est;
            t0_tasks[0] = i;
            u_t0 = 1;
          } else if (est == t0) {
            t0_tasks[u_t0++] = i;
          }
        }
        int t_j0m0;
        if (iteration == 0) {
          // In the first iteration, select tasks with longest processing time
          t_j0m0 = 0;
          for (int i=1; i<u_t0; i++)
            if (tasks[t0_tasks[i]].p > tasks[t0_tasks[t_j0m0]].p)
              t_j0m0 = i;
        } else {
          t_j0m0 = rnd(u_t0); // Select random task
        }
        const Task& t = tasks[t0_tasks[t_j0m0]];
        int ect = t0 + t.p;
        ct_j[t.j] = ect;
        ct_m[t.m] = ect;
        std::swap(tasks[--u],tasks[t0_tasks[t_j0m0]]); // Remove task from u
        cmax = std::max(cmax, ect);
        if (cmax > maxmakespan)
          break;
      }
      
      maxmakespan = std::min(maxmakespan,cmax);
      if (iteration++ > maxIterations)
        stopCROSH = true; // Iterate a couple of times
    }
  }
public:
  /// The actual problem
  OpenShop(const SizeOptions& opt)
    : IntMinimizeScript(opt),
      spec(examples[opt.size()]),
      b(*this, (spec.n+spec.m-2)*spec.n*spec.m/2, 0,1),
      makespan(*this, 0, Int::Limits::max),
      _start(*this, spec.m*spec.n, 0, Int::Limits::max) {

    Matrix<IntVarArray> start(_start, spec.m, spec.n);
    IntArgs _dur(spec.m*spec.n, spec.p);
    Matrix<IntArgs> dur(_dur, spec.m, spec.n);

    int minmakespan;
    int maxmakespan;
    crosh(dur, minmakespan, maxmakespan);
    rel(*this, makespan <= maxmakespan);
    rel(*this, makespan >= minmakespan);

    int k=0;
    for (int m=0; m<spec.m; m++)
      for (int j0=0; j0<spec.n-1; j0++)
        for (int j1=j0+1; j1<spec.n; j1++) {
          // The tasks on machine m of jobs j0 and j1 must be disjoint
          rel(*this,
              b[k] == (start(m,j0) + dur(m,j0) <= start(m,j1)));
          rel(*this,
              b[k++] == (start(m,j1) + dur(m,j1) > start(m,j0)));
        }
    
    for (int j=0; j<spec.n; j++)
      for (int m0=0; m0<spec.m-1; m0++)
        for (int m1=m0+1; m1<spec.m; m1++) {
          // The tasks in job j on machine m0 and m1 must be disjoint
          rel(*this,
              b[k] == (start(m0,j) + dur(m0,j) <= start(m1,j)));
          rel(*this,
              b[k++] == (start(m1,j) + dur(m1,j) > start(m0,j)));
        }

    // The makespan is greater than the end time of the latest job
    for (int m=0; m<spec.m; m++) {
      for (int j=0; j<spec.n; j++) {
        rel(*this, start(m,j) + dur(m,j) <= makespan);
      }
    }

    // First branch over the precedences
    branch(*this, b, INT_VAR_AFC_MAX(opt.decay()), INT_VAL_MAX());
    // When the precedences are fixed, simply assign the start times
    assign(*this, _start, INT_ASSIGN_MIN());
    // When the start times are fixed, use the tightest makespan
    assign(*this, makespan, INT_ASSIGN_MIN());
  }

  /// Constructor for cloning \a s
  OpenShop(bool share, OpenShop& s) : IntMinimizeScript(share,s), spec(s.spec) {
    b.update(*this, share, s.b);
    makespan.update(*this, share, s.makespan);
    _start.update(*this, share, s._start);
  }

  /// Perform copying during cloning
  virtual Space*
  copy(bool share) {
    return new OpenShop(share,*this);
  }

  /// Minimize the makespan
  virtual IntVar
  cost(void) const {
    return makespan;
  }

  /// Helper class for representing tasks when printing a solution
  class PrintTask {
  public:
    int start; //< Start time
    int job;   //< Job number
    int p;     //< Processing time
    /// Comparison of tasks based on start time, used for sorting
    bool operator()(const PrintTask& t1, const PrintTask& t2) {
      return t1.start < t2.start;
    }
  };

  /// Print solution
  virtual void
  print(std::ostream& os) const {
    Region re(*this);
    PrintTask* m = re.alloc<PrintTask>(spec.n);
    for (int i=0; i<spec.m; i++) {
      int k=0;
      for (int j=0; j<spec.n; j++) {
        m[k].start = _start[i*spec.n+j].val();
        m[k].job = j;
        m[k].p = spec.p[i*spec.n+j];
        k++;
      }
      Support::quicksort(m, spec.n, m[0]);
      os << "Machine " << i << ": ";
      for (int j=0; j<spec.n; j++)
        os << "\t" << m[j].job << "("<<m[j].p<<")";
      os << " = " << m[spec.n-1].start+m[spec.n-1].p << std::endl;
    }
    os << "Makespan: " << makespan << std::endl;
  }
  
};

/** \brief Main-function
 *  \relates OpenShop
 */
int main(int argc, char* argv[]) {
  SizeOptions opt("OpenShop");
  opt.iterations(5000);
  opt.size(0);
  opt.parse(argc,argv);
  if (opt.size() >= n_examples) {
    std::cerr << "Error: size must be between 0 and "
              << n_examples-1 << std::endl;
    return 1;
  }
  opt.solutions(0);
  IntMinimizeScript::run<OpenShop,BAB,SizeOptions>(opt);
  return 0;
}

namespace {

  /** \name Open shop specifications
   *
   * Each specification gives the processing times of the tasks for each
   * job, as well as the number of jobs and machines.
   *
   * \relates OpenShop
   */
  //@{

  const int ma2_p[] = {
    25, 30,
    32, 31
  };

  OpenShopSpec ma2(2,2,ma2_p);

  const int ma3_p[] = {
   55, 75, 81,
   20, 33, 15,
   10, 30, 100
  };
  OpenShopSpec ma3(3,3,ma3_p);

  const int ma4_p[] = {
   81, 33, 35, 43,
   12, 43, 44, 22,
   100, 101, 45, 34,
   80, 22, 30, 99
  };
  OpenShopSpec ma4(4,4,ma4_p);

  const int ma5_p[] = {
   53, 29, 35, 43, 11,
   12, 43, 44, 22, 53,
   34, 101, 45, 34, 34,
   45, 43, 32, 100, 77,
   32, 10, 15, 34, 54
  };
  OpenShopSpec ma5(5,5,ma5_p);

  const int ma6_p[] = {
    45,43,42,41,43,43,
    49,35,47,43,36,37,
    44,47,47,45,43,46,
    42,37,49,35,40,40,
    48,36,45,35,50,37,
    49,48,40,42,44,50
  };
  OpenShopSpec ma6(6,6,ma6_p);

  const int ma7_p[] = {
    45,43,42,41,43,43,35,
    49,35,47,43,36,37,41,
    44,47,47,45,43,46,50,
    42,37,49,35,40,40,50,
    48,36,45,35,50,37,34,
    49,48,40,42,44,50,23,
    30,43,42,13,34,42,20
  };
  OpenShopSpec ma7(7,7,ma7_p);

  const int ma8_p[] = {
    45,43,42,41,43,43,35,35,
    49,35,47,43,36,37,41,43,
    44,47,47,45,43,46,50,32,
    42,37,49,35,40,40,50,41,
    48,36,45,35,50,37,34,29,
    49,48,40,42,44,50,23,30,
    30,43,42,13,34,42,20,53,
    50,50,32,53,43,42,32,37
  };
  OpenShopSpec ma8(8,8,ma8_p);

  const int ma9_p[] = {
    45,43,42,41,43,43,35,35,32,
    49,35,47,43,36,37,41,43,45,
    44,47,47,45,43,46,50,32,49,
    42,37,49,35,40,40,50,41,42,
    48,36,45,35,50,37,34,29,30,
    49,48,40,42,44,50,23,30,44,
    30,43,42,13,34,42,20,53,40,
    50,50,32,53,43,42,32,37,53,
    47,43,34,29,23,50,32,32,33
  };
  OpenShopSpec ma9(9,9,ma9_p);


  const int ma10_p[] = {
    48,45,49,47,38,40,42,37,41,39,
    49,49,48,38,41,36,38,38,37,48,
    35,48,43,48,46,46,50,38,50,44,
    35,46,50,40,48,45,41,41,37,40,
    44,41,45,49,36,43,37,41,49,41,
    50,47,47,39,39,46,35,47,43,43,
    38,40,36,40,37,46,44,42,40,38,
    43,37,41,43,36,38,38,39,39,44,
    47,50,48,48,50,46,50,37,43,36,
    35,42,37,49,44,37,48,44,38,44
  };
  OpenShopSpec ma10(10,10,ma10_p);

  const int ma11_p[] = {
    48,45,49,47,38,40,42,37,41,39,30,
    49,49,48,38,41,36,38,38,37,48,40,
    35,48,43,48,46,46,50,38,50,44,36,
    35,46,50,40,48,45,41,41,37,40,46,
    44,41,45,49,36,43,37,41,49,41,42,
    50,47,47,39,39,46,35,47,43,43,29,
    38,40,36,40,37,46,44,42,40,38,32,
    43,37,41,43,36,38,38,39,39,44,33,
    47,50,48,48,50,46,50,37,43,36,38,
    35,42,37,49,44,37,48,44,38,44,43,
    35,44,37,34,38,42,39,45,32,44,31
  };
  OpenShopSpec ma11(11,11,ma11_p);

  const int ma12_p[] = {
    48,45,49,47,38,40,42,37,41,39,30,28,
    49,49,48,38,41,36,38,38,37,48,40,34,
    35,48,43,48,46,46,50,38,50,44,36,23,
    35,46,50,40,48,45,41,41,37,40,46,42,
    44,41,45,49,36,43,37,41,49,41,42,42,
    50,47,47,39,39,46,35,47,43,43,29,33,
    38,40,36,40,37,46,44,42,40,38,32,38,
    43,37,41,43,36,38,38,39,39,44,33,33,
    47,50,48,48,50,46,50,37,43,36,38,50,
    35,42,37,49,44,37,48,44,38,44,43,49,
    35,44,37,34,38,42,39,45,32,44,31,53,
    35,37,41,46,50,50,50,46,48,48,49,45
  };
  OpenShopSpec ma12(12,12,ma12_p);

  const int ma13_p[] = {
    48,45,49,47,38,40,42,37,41,39,30,28,31,
    49,49,48,38,41,36,38,38,37,48,40,34,32,
    35,48,43,48,46,46,50,38,50,44,36,23,43,
    35,46,50,40,48,45,41,41,37,40,46,42,43,
    44,41,45,49,36,43,37,41,49,41,42,42,43,
    50,47,47,39,39,46,35,47,43,43,29,33,43,
    38,40,36,40,37,46,44,42,40,38,32,38,43,
    43,37,41,43,36,38,38,39,39,44,33,33,43,
    47,50,48,48,50,46,50,37,43,36,38,50,43,
    35,42,37,49,44,37,48,44,38,44,43,49,43,
    35,44,37,34,38,42,39,45,32,44,31,53,43,
    35,37,41,46,50,50,50,46,48,48,49,45,43,
    41,43,34,24,53,23,45,55,51,43,34,23,43

  };
  OpenShopSpec ma13(13,13,ma13_p);

  const int ma14_p[] = {
    48,45,49,47,38,40,42,37,41,39,30,28,31,32,
    49,49,48,38,41,36,38,38,37,48,40,34,32,34,
    35,48,43,48,46,46,50,38,50,44,36,23,43,23,
    35,46,50,40,48,45,41,41,37,40,46,42,43,37,
    44,41,45,49,36,43,37,41,49,41,42,42,43,43,
    50,47,47,39,39,46,35,47,43,43,29,33,43,32,
    38,40,36,40,37,46,44,42,40,38,32,38,43,33,
    43,37,41,43,36,38,38,39,39,44,33,33,43,50,
    47,50,48,48,50,46,50,37,43,36,38,50,43,43,
    35,42,37,49,44,37,48,44,38,44,43,49,43,37,
    35,44,37,34,38,42,39,45,32,44,31,53,43,33,
    35,37,41,46,50,50,50,46,48,48,49,45,43,42,
    41,43,34,24,53,23,45,55,51,43,34,23,43,42,
    44,41,45,49,36,43,37,41,49,41,42,42,43,32
  };
  OpenShopSpec ma14(14,14,ma14_p);

  const int ma5a_p[] = {
   53, 29, 35, 43, 11,
   12, 43, 44, 22, 53,
   34, 101, 45, 34, 34,
   45, 43, 32, 100, 77,
   32, 10, 15, 34, 54
  };
  OpenShopSpec ma5a(2,10,ma5a_p);

  const int ma5b_p[] = {
   53, 29, 35, 43, 11,
   12, 43, 44, 22, 53,
   34, 101, 45, 34, 34,
   45, 43, 32, 100, 77,
   32, 10, 15, 34, 54
  };
  OpenShopSpec ma5b(10,2,ma5b_p);
                          //  0     1   2     3     4     5   6     7   8     9     10    11    12    13    14
  OpenShopSpec examples[] = { ma2, ma3, ma4, ma5, ma5a, ma5b, ma6, ma7, ma8, ma9, ma10, ma11, ma12, ma13, ma14 };
  const unsigned int n_examples = sizeof(examples) / sizeof(OpenShopSpec);

  //@}
}