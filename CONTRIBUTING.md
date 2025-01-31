# How to contribute with git

- Contribute as usual on the private repo
- If you want to push something to the public repo you can:
    - checkout the `public` branch: `git checkout public`
    - squash merge the branch you’ve been working on (say it is called `mybr`): `git merge --squash mybr`
    - commit (this will be the only commit that will be created): `git commit -am "Implemented feature X"`
    - push to the public remote `git push public public`

# Setup details: how to create the public repo (for future reference)

- create a new public empty repo with url `pub_url`
- in the private repo
    - create a branch with no history (orphan): `git checkout —orphan public` and `git commit -am "First public commit!"`
    - add the remote of the public repo: `git remote add public <pub_url>`
    - do the first push: `git push public public`
    - after that, the public repo includes the code from `public` without any history
