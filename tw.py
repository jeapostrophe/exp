### News source
class NewsSource(object):
    def login(self, config, section):
        the_app_key = config.get(section, "app_key")
        the_app_secret = config.get(section, "app_secret")

        if not config.has_option(section, "oauth_token"):
            if not config.has_option(section, "auth_verifier"):
                t = self.connect(app_key = the_app_key,
                                 app_secret = the_app_secret )
                auth_props = t.get_authentication_tokens()
                print "Go to this URL: %s" % auth_props['auth_url']
                print "Then, add the verifier to the config file as the option auth_verifier under section %s" % section
                config.set(section, "auth_token", auth_props['oauth_token'])
                config.set(section, "auth_token_secret", auth_props['oauth_token_secret'])
                save_config()
                exit(0)

                t = self.connect(
                    app_key = the_app_key,
                    app_secret = the_app_secret,
                    oauth_token = config.get(section, "auth_token"),
                    oauth_token_secret = config.get(section, "auth_token_secret") )
                authorized_tokens = t.get_access_token(config.get(section, "auth_verifier"))
                config.set(section, "auth_token", authorized_tokens['oauth_token'])
                config.set(section, "auth_token_secret", authorized_tokens['oauth_token_secret'])
                save_config()

            return self.connect(
                app_key = the_app_key,
                app_secret = the_app_secret,
                oauth_token = config.get(section, "oauth_token"),
                oauth_token_secret = config.get(section, "oauth_token_secret") )

class TumblrNewsSource(NewsSource):
    def connect(self, app_key = None, app_secret = None, oauth_token = None, oauth_token_secret = None):
        return Tumblpy(app_key = app_key,
                       app_secret = app_secret,
                       oauth_token = oauth_token,
                       oauth_token_secret = oauth_token_secret )

class TwitterNewsSource(NewsSource):
    def connect(self, app_key = None, app_secret = None, oauth_token = None, oauth_token_secret = None):
        return Twython(twitter_token = app_key,
                       twitter_secret = app_secret,
                       oauth_token = oauth_token,
                       oauth_token_secret = oauth_token_secret )

### Configuration
import ConfigParser
from os.path import expanduser

config_path = expanduser("~/.tw.ini")
def save_config ():
    with open(config_path, 'w') as config_fd:
        config.write(config_fd)

config = ConfigParser.RawConfigParser()
config.read(config_path)

from twython import Twython
tw1 = TwitterNewsSource().login(config, "twitter1")
tw2 = TwitterNewsSource().login(config, "twitter2")

results = tw1.getHomeTimeline(count = 200)
for t in results:
    t['id']
    print "@%s: %s (%s)" % (t['user']['screen_name'], t['text'], t['created_at'])

from tumblpy import Tumblpy
tu = TumblrNewsSource().login(config, "tumblr")
print len(tu.get('user/dashboard', params = {'offset': 20})['posts'])

# XXX Both:
# XXXX Remember last entry, get them all since then, produce an rss feed
