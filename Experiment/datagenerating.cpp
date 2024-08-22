#include <iostream>
#include <vector>
#include <unordered_map>
#include <ctime>
#include <string>
#include <cmath>


using namespace std;
// 重复模式函数
string repetition(int n) {
    string cond;
    for (int i = 1; i < n; ++i){
        cond += "(1,0," + to_string(i) + ")";
        cond += "(1,0," + to_string(i + 1) + ")&&";
    }
    cond += "(-1)^b_(1)";
    for (int i = 1; i <= n; ++i) {
        cond += "(1,0," + to_string(i) + ")";
    }
    return cond;
}

// 表面代码函数
unordered_map<int, vector<int> > surface(int n) {
    int t = n / 2 + 1;
    unordered_map<int, vector<int> > x_inds;
    unordered_map<int, vector<int> > z_inds;
    for (int i = 1; i < t; i++) {
        for (int j = 1; j < t; j++) {
            int topl = (2 * i - 2) * n + (2 * j - 1);
            cout << topl << endl;
            x_inds[topl] = vector<int>();
            x_inds[topl].push_back(topl);
            x_inds[topl].push_back(topl + 1);
            x_inds[topl].push_back(topl + n);
            x_inds[topl].push_back(topl + n + 1);
        }
    }
    return x_inds;
}

int main() {
    int n = 71;


    // 计算开始时间
    clock_t start = clock();

    // 调用 surface 函数
    unordered_map<int, vector<int> > result = surface(n);

    // 计算结束时间
    clock_t end = clock();
    double elapsed_time = double(end - start) / CLOCKS_PER_SEC;

    

    // 打印运行时间
    cout << "Elapsed time: " << elapsed_time << " seconds" << endl;

    return 0;
}
