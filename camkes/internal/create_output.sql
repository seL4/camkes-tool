create table if not exists output (
    id integer primary key autoincrement,
    argv text not null,
    cwd text not null,
    sha256 text not null);
