#ifndef intervalAnalysis_HEADER
#define intervalAnalysis_HEADER

#include <map>

class Interval {
    private :
        uint64_t lo;
        uint64_t hi;
    public :
        Interval ();
        Interval (uint64_t lo, uint64_t hi);

        uint64_t g_lo () { return lo; }
        uint64_t g_hi () { return hi; }

        void s_lo (uint64_t lo) { this->lo = lo; }
        void s_hi (uint64_t hi) { this->hi = hi; }

        std::string string () {
            char buf[128];
            snprintf(buf, 128, "[%llx, %llx]", lo, hi);
            buf[127] = '\0';
            return buf;
        }
};

class IntervalAnalysis {
    private :
        std::map <std::string, Interval> intervals;

    public :
        IntervalAnalysis (const QuesoGraph * quesoGraph);

        std::map <std::string, Interval> g_intervals () {
            return intervals;
        }
};

#endif