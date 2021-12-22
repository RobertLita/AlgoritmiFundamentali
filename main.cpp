#include <iostream>
#include <vector>
#include <fstream>
#include <queue>
#include <stack>
#include <algorithm>
#define nmax 100010
#define inf 1 << 29
using namespace std;

ifstream f("hamilton.in");
ofstream g("hamilton.out");

class Graf{
private:
    vector<vector<int>> la;
    vector<vector<int>> la_t;
    int par[nmax];
    int dim[nmax];
    vector<int> topo;
    int dist[nmax] = {-1};
    bool viz[nmax] = {false};
    int n, m, componente_conexe;

public:
    Graf(): n(0), m(0), componente_conexe(0){ }
    Graf(int x, int y = 0): n(x), m(y), componente_conexe(0){ }
    Graf(int x, int y, const vector<vector<int>>& v): n(x), m(y), componente_conexe(0), la(v) { }
    void dfs(int nod)
    {
        viz[nod] = true;
        for(auto i : la[nod])
            if(!viz[i])
                dfs(i);
    }

    int nr_componente()
    {
        for(int i = 1; i <= n; i++)
            if(!viz[i]) {
                dfs(i);
                componente_conexe++;
            }
        return componente_conexe;
    }

    void bfs(int nod)
    {
        int c[nmax],p = 0,u = -1;
        c[++u] = nod;
        dist[nod] = 0;
        while(p <= u)
        {
            int x = c[p];
            for(auto i:la[x])
                if(dist[i] == -1)
                {
                    c[++u] = i;
                    dist[i] = dist[x] + 1;
                }
            p++;
        }
    }

    void gol_viz()
    {
        for(int i = 1; i <= n; i++)
            viz[i] = false;
    }
    void ctc(int nr_comp, int comp[], const vector<vector<int>>& ctc)
    {

        gol_viz();
        for(int i = 1; i <= n; i++)
            if(!viz[i])
                sorare_topologica(i);
        reverse(topo.begin(), topo.end());
        for(auto i:topo)
        {
            if(comp[i] == 0)
            {
                nr_comp++;
                gol_viz();
                dfs_t(i, nr_comp, ctc, comp);
            }
        }
    }

    void dfs_t(int nod, int nr_comp, vector<vector<int>> ctc, int comp[])
    {
        viz[nod] = true;
        comp[nod] = nr_comp;
        ctc[nr_comp].push_back(nod);
        for(auto i:la_t[nod])
            if(!viz[i])
                dfs_t(i, nr_comp, ctc, comp);
    }

    void sorare_topologica(int nod)
    {
        viz[nod] = true;
        for(auto i:la[nod])
        {
            if(viz[i] == 0)
                sorare_topologica(i);
        }
        topo.push_back(nod);
    }

    bool hakimi(vector<int> &grade)
    {
        sort(grade.begin(), grade.end(), greater<>());
        while(!grade.empty())
        {
            if(grade[0] + 1 > grade.size())
                return false;
            for(int i = 1; i <= grade[0]; ++i)
            {
                grade[i]--;
                if(grade[i] < 0)
                    return false;
            }
            grade.erase(grade.begin());
            sort(grade.begin(), grade.end(), greater<>());
        }
        return true;
    }
    void init()
    {
        for(int i = 1;i <= n;++i) {
            par[i] = i;
            dim[i] = 1;
        }
    }
    int find(int x) {
        int xx = x, aux;
        while(x != par[x]) {
            x = par[x];
        }
        while(xx != x){
            aux = par[xx];
            par[xx] = x;
            xx = aux;
        }
        return x;

    }

    void unite(int x, int y)
    {
       x = find(x);
       y = find(y);
        if(dim[x] >= dim[y])
        {
            par[y] = x;
            dim[x] += dim[y];
        }
        else
        {
            par[y] = x;
            dim[y] += dim[x];
        }
    }
    vector<pair<int, pair<int, int>>> kruskal(vector<pair<int, pair<int, int>>>& muchii)
    {
        vector<pair<int, pair<int, int>>> solutie;
        sort(muchii.begin(), muchii.end());
        init();
        for(auto &muchie : muchii)
        {
            if(find(muchie.second.first) != find(muchie.second.second))
            {
                unite(muchie.second.first, muchie.second.second);
                solutie.push_back({muchie.first, {muchie.second.first, muchie.second.second}});
            }
        }
        return solutie;
    }

    vector<int> bellman_ford(int start, vector<pair<int, int>> g[])
    {
        vector<int> D(nmax / 2, 1 << 30);
        vector<int> cnt(nmax / 2);
        queue<int> q;
        q.push(start);
        D[start] = 0;
        bool are_ciclu = false;
        while(!q.empty() && !are_ciclu){
            int nod = q.front();
            q.pop();
            viz[nod] = false;
            for(auto x : g[nod]){
                if(D[nod] + x.second < D[x.first]){
                    if(!viz[x.first]){
                        q.push(x.first);
                        cnt[x.first]++;
                        viz[x.first] = true;
                        if(cnt[x.first] > n)
                            are_ciclu = true;

                    }
                    D[x.first] = D[nod] + x.second;
                }
            }
        }
        if(are_ciclu)D[start] = -1;
        return D;
    }

    vector<int> dijkstra(int start, vector<pair<int, int>> g[])
    {
        priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> q;
        vector<int> D(nmax / 2, 1 << 30);
        D[start] = 0;
        q.push({0, start});
        while(!q.empty()){
            int nod = q.top().second;
            q.pop();
            if (!viz[nod]) {
                viz[nod] = true;
                for (auto x : g[nod])
                    if (D[nod] + x.second < D[x.first]) {
                        D[x.first] = D[nod] + x.second;
                        q.push({D[x.first], x.first});
                    }
            }
        }
        return D;
    }

    void royfloyd(int c[][105]) const{
        for(int k = 1; k <= n; k++)
            for(int i = 1; i <= n; i++)
                for(int j = 1; j <= n; j++)
                    if(c[i][k] + c[k][j] < c[i][j])
                        c[i][j] = c[i][k] + c[k][j];
    }
    void dfs_diametru(int x, int d, int &dmax, int &nodmax){
        if (d > dmax){
            dmax = d;
            nodmax = x;
        }
        viz[x] = true;
        for (auto i : la[x]){
            if (!viz[i]){
                dfs_diametru(i, d+1, dmax, nodmax);
            }
        }

    }
    int diametru(){
        int nodmax = 0, dmax = 0;
        dfs_diametru(1,0,dmax,nodmax);
        int nod1 = nodmax;
        gol_viz();
        dmax = 0;
        nodmax = 0;
        dfs_diametru(nod1, 0, dmax, nodmax);
        return dmax + 1;
    }

    void ciclu_Eulerian(int start, vector<pair<int, int>> l[], vector<int> &c){
        stack <int> stiva;
        //gol_viz();
        stiva.push(start);
        while(!stiva.empty())
        {
            int nod = stiva.top();
            if(!l[nod].empty())
            {
                int vecin = l[nod].back().first;
                int nrMuchie = l[nod].back().second;
                l[nod].pop_back();
                if(!viz[nrMuchie])
                {
                    viz[nrMuchie] = true;
                    stiva.push(vecin);
                }
            }
            else
            {
                c.push_back(nod);
                stiva.pop();
            }
        }
    }

    void rez_Euler(vector<pair<int, int>> l[]){
        vector <int> ciclu;
        for(int i = 0; i <= n; i++)
        {
            if(l[i].size() % 2 == 1)
            {
                g << "-1";
                return;
            }
        }
        ciclu_Eulerian(1, l, ciclu);
        for(int i = 0; i < ciclu.size() - 1; i++)
        {
            g << ciclu[i] << " ";
        }
    }

    int HamiltonianMin(const vector<vector<int>>& cost){
        vector<vector<int>> c(1 << n);
        for (int i = 0; i < 1 << n; i++){
            c[i].resize(n, inf);
        }
        c[1][0] = 0;
        for(int i = 1; i < 1 << n; i++){
            for(int j = 0; j < n; j++){
                if(c[i][j] != inf){
                    for(auto &k : la[j]){
                        if(!(i & (1 << k)))
                            c[i | (1 << k)][k] = min(c[i | (1 << k)][k], c[i][j] + cost[j][k]);
                    }
                }
            }
        }
        vector<int> penult;
        int mn = inf;
        for(int i = 1; i < n ; i++)
            for(auto &k : la[i])
                if(k == 0) penult.push_back(i);
        for(auto &k : penult){
            mn = min(mn, c[(1 << n) - 1][k] + cost[k][0]);
        }
        return mn;
    }
};



int main()
{
    int n, m, x, y, c;
    f >> n >> m;
    vector<vector<int>> la(n);
    vector<vector<int>> cost(n);
    for(int i = 0; i < n; i++) {
        cost[i].resize(n, inf);
    }
    for(int i = 1; i <= m; i++){
        f >> x >> y >> c;
        la[x].push_back(y);
        la[y].push_back(x);
        cost[x][y] = c;
    }
    Graf graf(n, m, la);
    int mn = graf.HamiltonianMin(cost);
    if(mn == inf) g << "Nu exista solutie";
    else g << mn;
    return 0;
}
