#include <cstddef>
#include <vector>
#include <functional>
#include <cassert>
#include <iostream>
#include <algorithm>

using namespace std;

template<class T>
class Set {
public:
    struct vertex {
        const T *L;
        const T *R;
        const T *val;
        vertex *p;
        vector<vertex *> ch;

        vertex() : L(nullptr), R(nullptr), val(nullptr), p(nullptr), ch() {

        }
    };

    Set() : SZ(0), root(nullptr), beg(nullptr), en(nullptr) {
    }

    template<typename Iterator>
    Set(Iterator first, Iterator last): SZ(0), root(nullptr), beg(nullptr), en(nullptr) {
        while (first != last) {
            (*this).insert(*first);
            first = std::next(first);
        }
    }

    Set(std::initializer_list<T> elems) : SZ(0), root(nullptr), beg(nullptr), en(nullptr) {
        for (const T &elem: elems) {
            (*this).insert(elem);
        }
    }

    Set(const Set &other) : SZ(0), root(nullptr), beg(nullptr), en(nullptr) {
        if (other.root == nullptr) {
            root = nullptr;
            beg = nullptr;
            en = nullptr;
            SZ = 0;
            return;
        }
        SZ = other.SZ;
        root = new vertex;
        root->p = root;
        function<void(vertex *, vertex *)> dfs_to_deep_copy = [&](vertex *him, vertex *me) {
            if (him == nullptr)
                return;
            if (him->val != nullptr) {
                me->val = new const T(*him->val);
            } else
                me->val = nullptr;
            for (auto c: him->ch) {
                vertex *CH = new vertex;
                CH->p = me;
                me->ch.push_back(CH);
                dfs_to_deep_copy(c, CH);
            }
            if (me->ch.empty()) {
//                assert(me->val != nullptr);
                me->L = me->val;
                me->R = me->val;
            } else {
                me->L = me->ch[0]->L;
                me->R = me->ch.back()->R;
            }
        };
        dfs_to_deep_copy(other.root, root);
        beg = root;
        while (beg != nullptr && !beg->ch.empty())
            beg = beg->ch[0];
        en = root;
        while (en != nullptr && !en->ch.empty())
            en = en->ch.back();
    }

    Set &operator=(const Set &other) {
        if (this->root == other.root && this->beg == other.beg && this->en == other.en && this->SZ == other.SZ) {
            return *this;
        }
        function<void(vertex *)> dfs_to_delete = [&](vertex *s) {
            if (s == nullptr)
                return;
            for (vertex *c: s->ch) {
                dfs_to_delete(c);
            }
            delete s->val;
            delete s;
        };
        dfs_to_delete(root);
        if (other.root == nullptr) {
            root = nullptr;
            beg = nullptr;
            en = nullptr;
            SZ = 0;
            return *this;
        }
        SZ = other.SZ;
        root = new vertex;
        root->p = root;
        function<void(vertex *, vertex *)> dfs_to_deep_copy = [&](vertex *him, vertex *me) {
            if (him == nullptr)
                return;
            if (him->val != nullptr) {
                me->val = new const T(*him->val);
            } else
                me->val = nullptr;
            for (auto c: him->ch) {
                vertex *CH = new vertex;
                CH->p = me;
                me->ch.push_back(CH);
                dfs_to_deep_copy(c, CH);
            }
            if (me->ch.empty()) {
//                assert(me->val != nullptr);
                me->L = me->val;
                me->R = me->val;
            } else {
                me->L = me->ch[0]->L;
                me->R = me->ch.back()->R;
            }
        };
        dfs_to_deep_copy(other.root, root);
        beg = root;
        while (beg != nullptr && !beg->ch.empty())
            beg = beg->ch[0];
        en = root;
        while (en != nullptr && !en->ch.empty())
            en = en->ch.back();
        return *this;
    }

    ~Set() {
        function<void(vertex *)> dfs_to_delete = [&](vertex *s) {
            if (s == nullptr)
                return;
            for (vertex *c: s->ch) {
                dfs_to_delete(c);
            }
            delete s->val;
            delete s;
        };
        dfs_to_delete(root);
    }

    size_t size() const {
        return SZ;
    }

    bool empty() const {
        return SZ == 0;
    }

    bool is_equal(const T &elem1, const T &elem2) const {
        return !(elem1 < elem2) && !(elem2 < elem1);
    }

    vertex *new_term_vertex(const T &elem) {
        vertex *s = new vertex;
        s->ch = vector<vertex *>();
        s->val = new const T(elem);
        s->L = s->val;
        s->R = s->val;
        s->p = s;
        SZ++;
        return s;
    }

    vertex *new_vertex_with_ch(const vector<vertex *> &ch) {
//        assert(!ch.empty());
        vertex *s = new vertex;
        s->p = s;
        s->val = nullptr;
        s->ch = ch;
        sort(s->ch.begin(), s->ch.end(), [&](vertex *a, vertex *b) {
            return *a->L < *b->L;
        });
        s->L = s->ch[0]->L;
        s->R = s->ch.back()->R;
        for (const auto &to: s->ch) {
            to->p = s;
        }
        return s;
    }

    void rebuild_children(vertex *s, bool need_sort = true) {
        if (s->ch.empty())
            return;
        if (need_sort) {
            sort(s->ch.begin(), s->ch.end(), [&](vertex *a, vertex *b) {
                return *a->L < *b->L;
            });
        }
        s->L = s->ch[0]->L;
        s->R = s->ch.back()->R;
        for (const auto &to: s->ch) {
            to->p = s;
        }
    }

    bool is_terminal(vertex *v) const {
        return v->ch.empty();
    }

    void insert(const T &elem) {
        if (root == nullptr) {
            root = new_term_vertex(elem);
            beg = root;
            en = root;
        } else {
            if (SZ == 1) {
                if (is_equal(*root->val, elem)) {
                    return;
                }
                vertex *one_more = new_term_vertex(elem);
                if (elem < *beg->val)
                    beg = one_more;
                if (*en->val < elem)
                    en = one_more;
                root = new_vertex_with_ch({root, one_more});
            } else {
                vertex *now = root;
                while (!is_terminal(now->ch[0])) {
                    bool found = false;
                    for (auto c: now->ch) {
                        if (is_equal(elem, *c->R))
                            return;
                        if (elem < *c->R) {
                            found = true;
                            now = c;
                            break;
                        }
                    }
                    if (!found)
                        now = now->ch.back();
                }
                for (auto c: now->ch) {
                    if (is_equal(elem, *c->val))
                        return;
                }
                vertex *what = new_term_vertex(elem);
                if (elem < *beg->val)
                    beg = what;
                if (*en->val < elem)
                    en = what;
                now->ch.push_back(what);
                sort(now->ch.begin(), now->ch.end(), [&](vertex *a, vertex *b) {
                    return *a->L < *b->L;
                });
                function<void(vertex *)> solve_problems = [&](vertex *s) {
                    rebuild_children(s, false);
                    if (s->ch.size() == 4) {
                        vertex *brother = new_vertex_with_ch({s->ch[2], s->ch[3]});
                        s->ch.pop_back();
                        s->ch.pop_back();
                        rebuild_children(s, false);
                        if (s == s->p) {
                            vertex *new_root = new_vertex_with_ch({s, brother});
                            root = new_root;
                        } else {
                            s->p->ch.push_back(brother);
                            sort(s->p->ch.begin(), s->p->ch.end(), [&](vertex *a, vertex *b) {
                                return *a->L < *b->L;
                            });
                        }
                    }
//                    assert(2 <= s->ch.size() && s->ch.size() <= 3);
                    if (s->p == s)
                        return;
                    solve_problems(s->p);
                };
                solve_problems(now);
            }
        }
    }

    void erase(const T &elem) {
        if (root == nullptr) {
            return;
        } else {
            if (SZ == 1) {
                if (is_equal(*root->val, elem)) {
                    delete root->val;
                    delete root;
                    root = nullptr;
                    beg = nullptr;
                    en = nullptr;
                    SZ--;
                }
                return;
            } else {
                vertex *now = root;
                while (!is_terminal(now->ch[0])) {
                    bool found = false;
                    for (auto c: now->ch) {
//                        assert(c->R != nullptr);
                        if (elem < *c->R || is_equal(elem, *c->R)) {
                            found = true;
                            now = c;
                            break;
                        }
                    }
                    if (!found)
                        return;
                }
                int ind = -1;
                for (int i = 0; i < now->ch.size(); i++) {
//                    assert(now->ch[i]->val != nullptr);
                    if (is_equal(elem, *now->ch[i]->val)) {
                        ind = i;
                        break;
                    }
                }
                if (ind == -1)
                    return;
                if (beg == now->ch[ind]) {
                    beg = (++iterator(beg, en)).now_;
                }
                if (en == now->ch[ind]) {
                    en = (--iterator(en, en)).now_;
                }
                SZ--;
                delete now->ch[ind]->val;
                delete now->ch[ind];
                now->ch.erase(now->ch.begin() + ind);
                function<void(vertex *)> solve_problems = [&](vertex *s) {
//                    assert(s != nullptr);
                    rebuild_children(s, false);
                    if (s->ch.size() == 1) {
//                        assert(s->p != nullptr);
                        if (s->p == s) {
//                            assert(!s->ch.empty());
//                            assert(s == root);
                            root = s->ch[0];
                            root->p = root;
//                            assert(s->val == nullptr);
                            delete s;
                            s = root;
                        } else {
                            vertex *P = s->p;
                            int what = -1;
                            for (int i = 0; i < P->ch.size(); i++) {
                                if (P->ch[i] == s)
                                    what = i;
                            }
//                            assert(what != -1);
//                            assert(2 <= P->ch.size() && P->ch.size() <= 3);
                            if (what + 1 < P->ch.size() && P->ch[what + 1]->ch.size() == 3) {
                                vertex *brother = P->ch[what + 1];
                                s->ch.push_back(brother->ch[0]);
                                brother->ch.erase(brother->ch.begin());
                                rebuild_children(s, false);
                                rebuild_children(brother, false);
                            } else if (what - 1 >= 0 && P->ch[what - 1]->ch.size() == 3) {
                                vertex *brother = P->ch[what - 1];
                                s->ch.insert(s->ch.begin(), brother->ch.back());
                                brother->ch.pop_back();
                                rebuild_children(s, false);
                                rebuild_children(brother, false);
                            } else if (what + 1 < P->ch.size()) {
                                vertex *brother = P->ch[what + 1];
//                                assert(brother->ch.size() == 2);
                                s->ch.push_back(brother->ch[0]);
                                s->ch.push_back(brother->ch[1]);
                                delete brother;
                                rebuild_children(s, false);
                                P->ch.erase(P->ch.begin() + what + 1);
                            } else {
                                vertex *brother = P->ch[what - 1];
//                                assert(brother->ch.size() == 2);
                                s->ch.push_back(brother->ch[1]);
                                s->ch.push_back(brother->ch[0]);
                                reverse(s->ch.begin(), s->ch.end());
                                delete brother;
                                rebuild_children(s, false);
                                P->ch.erase(P->ch.begin() + what - 1);
                            }
                        }
                    }
//                    assert((2 <= s->ch.size() && s->ch.size() <= 3) || is_terminal(s));

                    if (s->p == s)
                        return;
                    solve_problems(s->p);
                };
                solve_problems(now);
            }
        }
    }

    class iterator {
    public:

        iterator()
                : now_(nullptr), en_(nullptr) {
        }

        iterator(vertex *now, vertex *en)
                : now_(nullptr), en_(nullptr) {
            now_ = now;
            en_ = en;
        }

        iterator(const iterator &other)
                : now_(nullptr), en_(nullptr) {
            now_ = other.now_;
            en_ = other.en_;
        }

        iterator &operator=(const iterator &other) {
            now_ = other.now_;
            en_ = other.en_;
            return *this;
        }

        bool operator!=(const iterator &other) const {
            return this->now_ != other.now_;
        };

        bool operator==(const iterator &other) const {
            return this->now_ == other.now_;
        };


        iterator &operator++() {
            while (now_ != nullptr && now_ != now_->p) {
                int ind = -1;
                vertex *P = now_->p;
                for (int i = 0; i < P->ch.size(); i++) {
                    if (P->ch[i] == now_)
                        ind = i;
                }
//                assert(ind != -1);
                if (ind + 1 == P->ch.size()) {
                    now_ = now_->p;
                } else {
                    now_ = P->ch[ind + 1];
                    while (!now_->ch.empty())
                        now_ = now_->ch[0];
                    return *this;
                }
            }
            now_ = nullptr;
            return *this;
        };

        iterator operator++(int) {
            vertex *was = now_;
            while (now_ != nullptr && now_ != now_->p) {
                int ind = -1;
                vertex *P = now_->p;
                for (int i = 0; i < P->ch.size(); i++) {
                    if (P->ch[i] == now_)
                        ind = i;
                }
//                assert(ind != -1);
                if (ind + 1 == P->ch.size()) {
                    now_ = now_->p;
                } else {
                    now_ = P->ch[ind + 1];
                    while (!now_->ch.empty())
                        now_ = now_->ch[0];
                    return iterator(was, en_);
                }
            }
            now_ = nullptr;
            return iterator(was, en_);
        };

        iterator &operator--() {
            if (now_ == nullptr) {
                now_ = en_;
                return *this;
            }
            while (now_ != nullptr && now_ != now_->p) {
                int ind = -1;
                vertex *P = now_->p;
                for (int i = 0; i < P->ch.size(); i++) {
                    if (P->ch[i] == now_)
                        ind = i;
                }
//                assert(ind != -1);
                if (ind == 0) {
                    now_ = now_->p;
                } else {
                    now_ = P->ch[ind - 1];
                    while (!now_->ch.empty())
                        now_ = now_->ch.back();
                    return *this;
                }
            }
            now_ = nullptr;
            return *this;
        };

        iterator operator--(int) {
            if (now_ == nullptr) {
                now_ = en_;
                return iterator(nullptr, en_);
            }
            vertex *was = now_;
            while (now_ != now_->p) {
                int ind = -1;
                vertex *P = now_->p;
                for (int i = 0; i < P->ch.size(); i++) {
                    if (P->ch[i] == now_)
                        ind = i;
                }
//                assert(ind != -1);
                if (ind == 0) {
                    now_ = now_->p;
                } else {
                    now_ = P->ch[ind - 1];
                    while (!now_->ch.empty())
                        now_ = now_->ch.back();
                    return iterator(was, en_);
                }
            }
            now_ = nullptr;
            return iterator(was, en_);
        };

        const T operator*() const {
//            assert(now_ != nullptr);
//            assert(now_->val != nullptr);
            return *now_->val;
        };

        const T *operator->() const {
            return now_->val;
        };

        vertex *now_;
        vertex *en_;
    };


    iterator begin() const {
        return iterator(beg, en);
    }

    iterator end() const {
        return iterator(nullptr, en);
    }

    iterator find(const T &elem) const {
        if (root == nullptr) {
            return this->end();
        } else {
            if (SZ == 1) {
                if (is_equal(*root->val, elem)) {
                    return iterator(root, en);
                }
            } else {
                vertex *now = root;
                while (!is_terminal(now->ch[0])) {
                    bool found = false;
                    for (auto c: now->ch) {
                        if (elem < *c->R || is_equal(elem, *c->R)) {
                            found = true;
                            now = c;
                            break;
                        }
                    }
                    if (!found)
                        return this->end();
                }
                for (int i = 0; i < now->ch.size(); i++) {
//                    assert(now->ch[i]->val != nullptr);
                    if (is_equal(elem, *now->ch[i]->val)) {
                        return iterator(now->ch[i], en);
                    }
                }
                return this->end();
            }
        }
        return this->end();
    }

    iterator lower_bound(const T &elem) const {
        if (root == nullptr) {
            this->end();
        } else {
            if (SZ == 1) {
                if (*root->val < elem)
                    return this->end();
                else
                    return iterator(root, en);
            } else {
                vertex *now = root;
                while (!is_terminal(now->ch[0])) {
                    bool found = false;

                    for (auto c: now->ch) {
                        if (*c->R < elem) {
                            continue;
                        } else {
                            found = true;
                            now = c;
                            break;
                        }
                    }
                    if (!found)
                        return this->end();
                }

                for (auto c: now->ch) {
//                    assert(c->val != nullptr);
                    if (is_equal(elem, *c->val) || elem < *c->val)
                        return iterator(c, en);
                }

                return this->end();
            }
        }
        return this->end();
    }

private:
    int SZ;
    vertex *root;
    vertex *beg;
    vertex *en;
};
