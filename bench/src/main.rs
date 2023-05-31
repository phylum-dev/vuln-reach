//! Benchmark module loading performance.

use bytes::Bytes;
use vuln_reach::javascript::module::TarballModuleResolver;
use vuln_reach::javascript::package::Package;
use vuln_reach_upstream::javascript::module::TarballModuleResolver as UpstreamTarballModuleResolver;
use vuln_reach_upstream::javascript::package::Package as UpstreamPackage;

const PACKAGE_URIS: &[&str] = &[
    "https://registry.npmjs.org/codemirror/-/codemirror-5.5.0.tgz",
    "https://registry.npmjs.org/mongoose/-/mongoose-7.2.1.tgz",
    "https://registry.npmjs.org/core-js/-/core-js-3.30.2.tgz",

    "https://registry.npmjs.org/express/-/express-4.17.1.tgz",
    "https://registry.npmjs.org/lodash/-/lodash-4.17.21.tgz",
    "https://registry.npmjs.org/react/-/react-17.0.2.tgz",
    "https://registry.npmjs.org/axios/-/axios-0.21.1.tgz",
    "https://registry.npmjs.org/moment/-/moment-2.29.1.tgz",
    "https://registry.npmjs.org/dotenv/-/dotenv-10.0.0.tgz",
    "https://registry.npmjs.org/nodemon/-/nodemon-2.0.12.tgz",
    "https://registry.npmjs.org/mongoose/-/mongoose-6.0.5.tgz",
    "https://registry.npmjs.org/request/-/request-2.88.2.tgz",
    "https://registry.npmjs.org/cors/-/cors-2.8.5.tgz",
    "https://registry.npmjs.org/bcrypt/-/bcrypt-5.0.1.tgz",
    "https://registry.npmjs.org/socket.io/-/socket.io-4.1.2.tgz",
    "https://registry.npmjs.org/multer/-/multer-1.4.2.tgz",
    "https://registry.npmjs.org/joi/-/joi-17.4.0.tgz",
    "https://registry.npmjs.org/chalk/-/chalk-4.1.2.tgz",
    "https://registry.npmjs.org/fs-extra/-/fs-extra-10.0.0.tgz",
    "https://registry.npmjs.org/winston/-/winston-3.3.3.tgz",
    "https://registry.npmjs.org/helmet/-/helmet-4.6.0.tgz",
    "https://registry.npmjs.org/mysql/-/mysql-2.18.1.tgz",
    "https://registry.npmjs.org/jsonwebtoken/-/jsonwebtoken-8.5.1.tgz",
    "https://registry.npmjs.org/react-dom/-/react-dom-17.0.2.tgz",
    "https://registry.npmjs.org/jest/-/jest-27.0.6.tgz",
    "https://registry.npmjs.org/debug/-/debug-4.3.1.tgz",
    "https://registry.npmjs.org/axios-mock-adapter/-/axios-mock-adapter-1.19.0.tgz",
    "https://registry.npmjs.org/react-router-dom/-/react-router-dom-5.3.0.tgz",
    "https://registry.npmjs.org/firebase/-/firebase-8.8.1.tgz",
    "https://registry.npmjs.org/passport/-/passport-0.4.1.tgz",
    "https://registry.npmjs.org/morgan/-/morgan-1.10.0.tgz",
    "https://registry.npmjs.org/pg/-/pg-8.7.1.tgz",
    "https://registry.npmjs.org/prop-types/-/prop-types-15.7.2.tgz",
    "https://registry.npmjs.org/react-redux/-/react-redux-7.2.5.tgz",
    "https://registry.npmjs.org/nodemailer/-/nodemailer-6.6.3.tgz",
    "https://registry.npmjs.org/redux/-/redux-4.1.1.tgz",
    "https://registry.npmjs.org/moment-timezone/-/moment-timezone-0.5.34.tgz",
    "https://registry.npmjs.org/sequelize/-/sequelize-6.6.5.tgz",
    "https://registry.npmjs.org/cookie-parser/-/cookie-parser-1.4.5.tgz",
    "https://registry.npmjs.org/react-native-vector-icons/-/react-native-vector-icons-9.0.0.tgz",
    "https://registry.npmjs.org/passport-local/-/passport-local-1.0.0.tgz",
    "https://registry.npmjs.org/axios-cookiejar-support/-/axios-cookiejar-support-1.0.0.tgz",
    "https://registry.npmjs.org/express-validator/-/express-validator-6.12.1.tgz",
    "https://registry.npmjs.org/compression/-/compression-1.7.4.tgz",
    "https://registry.npmjs.org/rimraf/-/rimraf-3.0.2.tgz",
    "https://registry.npmjs.org/lodash.get/-/lodash.get-4.4.2.tgz",
    "https://registry.npmjs.org/lodash.merge/-/lodash.merge-4.6.2.tgz",
    "https://registry.npmjs.org/http-proxy-middleware/-/http-proxy-middleware-2.0.1.tgz",
    "https://registry.npmjs.org/mongoose-paginate-v2/-/mongoose-paginate-v2-1.4.3.tgz",
    "https://registry.npmjs.org/glob/-/glob-7.1.7.tgz",
    "https://registry.npmjs.org/chai/-/chai-4.3.4.tgz",
    "https://registry.npmjs.org/react-native-elements/-/react-native-elements-3.4.2.tgz",
    "https://registry.npmjs.org/express-session/-/express-session-1.17.2.tgz",
    "https://registry.npmjs.org/styled-components/-/styled-components-5.3.0.tgz",
    "https://registry.npmjs.org/bcryptjs/-/bcryptjs-2.4.3.tgz",
    "https://registry.npmjs.org/date-fns/-/date-fns-2.23.0.tgz",
    "https://registry.npmjs.org/concurrently/-/concurrently-6.4.0.tgz",
    "https://registry.npmjs.org/react-native-gesture-handler/-/react-native-gesture-handler-1.10.3.tgz",
    "https://registry.npmjs.org/formik/-/formik-2.2.9.tgz",
    "https://registry.npmjs.org/multer-s3/-/multer-s3-2.10.0.tgz",
    "https://registry.npmjs.org/socket.io-client/-/socket.io-client-4.3.2.tgz",
    "https://registry.npmjs.org/react-native-maps/-/react-native-maps-0.29.4.tgz",
    "https://registry.npmjs.org/helmet-csp/-/helmet-csp-3.0.0.tgz",
    "https://registry.npmjs.org/react-scripts/-/react-scripts-4.0.3.tgz",
    "https://registry.npmjs.org/mongoose-unique-validator/-/mongoose-unique-validator-3.0.0.tgz",
    "https://registry.npmjs.org/react-datepicker/-/react-datepicker-4.2.1.tgz",
    "https://registry.npmjs.org/passport-jwt/-/passport-jwt-4.0.0.tgz",
    "https://registry.npmjs.org/cheerio/-/cheerio-1.0.0-rc.3.tgz",
    "https://registry.npmjs.org/react-bootstrap/-/react-bootstrap-2.1.1.tgz",
    "https://registry.npmjs.org/dotenv-webpack/-/dotenv-webpack-7.0.3.tgz",
    "https://registry.npmjs.org/nodemailer-sendgrid-transport/-/nodemailer-sendgrid-transport-0.2.0.tgz",
    "https://registry.npmjs.org/winston-daily-rotate-file/-/winston-daily-rotate-file-4.5.2.tgz",
    "https://registry.npmjs.org/html-webpack-plugin/-/html-webpack-plugin-5.3.1.tgz",
    "https://registry.npmjs.org/typeorm/-/typeorm-0.2.36.tgz",
    "https://registry.npmjs.org/moment-duration-format/-/moment-duration-format-2.3.2.tgz",
    "https://registry.npmjs.org/cross-env/-/cross-env-7.0.3.tgz",
    "https://registry.npmjs.org/passport-facebook/-/passport-facebook-3.0.0.tgz",
    "https://registry.npmjs.org/redux-thunk/-/redux-thunk-2.4.0.tgz",
    "https://registry.npmjs.org/koa/-/koa-2.13.0.tgz",
    "https://registry.npmjs.org/react-native-navigation/-/react-native-navigation-7.15.0.tgz",
    "https://registry.npmjs.org/dotenv-flow/-/dotenv-flow-3.2.0.tgz",
    "https://registry.npmjs.org/cors-anywhere/-/cors-anywhere-0.4.4.tgz",
    "https://registry.npmjs.org/bodymen/-/bodymen-1.1.1.tgz",
    "https://registry.npmjs.org/axios-https-proxy-fix/-/axios-https-proxy-fix-0.17.1.tgz",
    "https://registry.npmjs.org/jsonwebtoken-promisified/-/jsonwebtoken-promisified-1.0.3.tgz",
    "https://registry.npmjs.org/jsonwebtoken-redis/-/jsonwebtoken-redis-1.0.6.tgz",
    "https://registry.npmjs.org/react-native-image-picker/-/react-native-image-picker-5.4.0.tgz",
    "https://registry.npmjs.org/jest-expect-message/-/jest-expect-message-1.1.3.tgz",
    "https://registry.npmjs.org/jest-mock-axios/-/jest-mock-axios-4.7.2.tgz",
    "https://registry.npmjs.org/csv-parser/-/csv-parser-3.0.0.tgz",
    "https://registry.npmjs.org/react-router/-/react-router-6.11.2.tgz",
    "https://registry.npmjs.org/morgan-body/-/morgan-body-2.6.9.tgz",
    "https://registry.npmjs.org/formik-material-ui/-/formik-material-ui-3.0.0.tgz",
    "https://registry.npmjs.org/debug-logdown/-/debug-logdown-0.2.0.tgz",
    "https://registry.npmjs.org/react-router-config/-/react-router-config-5.1.1.tgz",
    "https://registry.npmjs.org/@types/body-parser/-/body-parser-1.19.2.tgz",

    // TODO: Currently broken for one reason or another.
    // "https://registry.npmjs.org/react-native/-/react-native-0.64.2.tgz",
    // "https://registry.npmjs.org/yargs/-/yargs-17.0.1.tgz",
    // "https://registry.npmjs.org/react-native-camera/-/react-native-camera-4.2.0.tgz",
    // "https://registry.npmjs.org/sequelize-cli/-/sequelize-cli-6.2.0.tgz",
    // "https://registry.npmjs.org/vue/-/vue-2.6.14.tgz",
];

#[tokio::main]
async fn main() {
    for &package_uri in PACKAGE_URIS {
        println!("Benchmarking {package_uri}:");

        let tarball = reqwest::get(package_uri).await.unwrap().bytes().await.unwrap();

        // Time loading HEAD.
        let package = package(&tarball);

        // Time loading upstream.
        let upstream_package = upstream_package(&tarball);

        // Ensure equivalence.
        assert_eq(upstream_package, package);
    }
}

// Load package for the current revision.
fn package(tarball: &Bytes) -> Package<TarballModuleResolver> {
    let start = std::time::Instant::now();
    let package = Package::from_tarball_bytes(tarball.to_vec()).unwrap();
    println!("  HEAD loaded in {:?}", start.elapsed());

    package
}

// Load package for the upstream revision.
fn upstream_package(tarball: &Bytes) -> UpstreamPackage<UpstreamTarballModuleResolver> {
    let start = std::time::Instant::now();
    let package = UpstreamPackage::from_tarball_bytes(tarball.to_vec()).unwrap();
    println!("  Upstream loaded in {:?}", start.elapsed());

    package
}

// Check for equivalence of upstream/HEAD.
fn assert_eq(
    upstream: UpstreamPackage<UpstreamTarballModuleResolver>,
    head: Package<TarballModuleResolver>,
) {
    let upstream_graph = upstream.cache().graph();
    let graph = head.cache().graph();

    for (key, upstream_value) in upstream_graph {
        let value = match graph.get(key) {
            Some(value) => value,
            None => panic!("Missing key {key:?}"),
        };

        for (key, upstream_value) in upstream_value {
            assert_eq!(value.get(key), Some(upstream_value));
        }
    }
}
